//! Starlark diagnostics and shared Ty editor queries over captured sources.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::Write as _;
use std::sync::Arc;

use anyhow::{Context, Result, anyhow};
use lsp_server::{Connection, ErrorCode, Message as ServerMessage, Request, Response};
use lsp_types::{
    ClientCapabilities, Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity,
    DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams, ExitNotification, InitializeParams,
    Location, Notification as LspNotification, Position, PositionEncodingKind,
    PublishDiagnosticsNotification, PublishDiagnosticsParams, Range, Request as LspRequest,
    ServerCapabilities, ShutdownRequest, TextDocumentContentChangeEvent,
    TextDocumentContentChangePartial, TextDocumentContentChangeWholeDocument, TextDocumentSyncKind,
    TextDocumentSyncOptions, Uri,
};
use ruff_db::Db as _;
use ruff_db::diagnostic::{Diagnostic as SourceDiagnostic, Severity, Span, UnifiedFile};
use ruff_db::files::{File, FileRootKind, system_path_to_file};
use ruff_db::source::{line_index, source_text};
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_source_file::{LineIndex, OneIndexed, SourceLocation};
use ruff_text_size::{TextRange, TextSize};
use ty_starlark::analysis::{Analysis, CompletionKind};
use ty_starlark::bazel::{BazelRepository, find_bazel_repository};
use ty_starlark::graph::{analyze_bazel_graph, recover_bazel_graph};
use ty_starlark::source::BazelSource;

use crate::StyDb;
use crate::editor_system::{EditorSystem, OpenText};

mod star_host;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
enum Encoding {
    Utf8,
    Utf16,
    Utf32,
}

impl Encoding {
    fn negotiate(capabilities: &ClientCapabilities) -> Self {
        let encodings = capabilities
            .general
            .as_ref()
            .and_then(|general| general.position_encodings.as_ref());
        if encodings.is_some_and(|encodings| encodings.contains(&PositionEncodingKind::UTF8)) {
            Self::Utf8
        } else if encodings
            .is_some_and(|encodings| encodings.contains(&PositionEncodingKind::UTF16))
        {
            Self::Utf16
        } else if encodings
            .is_some_and(|encodings| encodings.contains(&PositionEncodingKind::UTF32))
        {
            Self::Utf32
        } else {
            // LSP's default position encoding is UTF-16.
            Self::Utf16
        }
    }

    fn kind(self) -> PositionEncodingKind {
        match self {
            Self::Utf8 => PositionEncodingKind::UTF8,
            Self::Utf16 => PositionEncodingKind::UTF16,
            Self::Utf32 => PositionEncodingKind::UTF32,
        }
    }

    fn source(self) -> ruff_source_file::PositionEncoding {
        match self {
            Self::Utf8 => ruff_source_file::PositionEncoding::Utf8,
            Self::Utf16 => ruff_source_file::PositionEncoding::Utf16,
            Self::Utf32 => ruff_source_file::PositionEncoding::Utf32,
        }
    }
}

struct OpenDocument {
    uri: Uri,
    version: i32,
    revision: u64,
}

struct Server {
    connection: Connection,
    db: StyDb,
    system: EditorSystem,
    documents: HashMap<SystemPathBuf, OpenDocument>,
    published: HashSet<Uri>,
    published_host: HashSet<Uri>,
    host_sources: Vec<star_host::HostSource>,
    host: Option<star_host::HostWorker>,
    bazel_analyses: Vec<Analysis>,
    host_analyses: BTreeMap<std::path::PathBuf, Analysis>,
    pending: VecDeque<ServerMessage>,
    encoding: Encoding,
    revision: u64,
    host_revision: u64,
    shutdown: bool,
    needs_bazel_check: bool,
    needs_host_check: bool,
}

pub(crate) fn run_stdio(cwd: &SystemPath) -> Result<()> {
    let (connection, io_threads) = Connection::stdio();
    run_connection(connection, cwd)?;
    io_threads.join().context("Sty language server I/O failed")
}

fn run_connection(connection: Connection, cwd: &SystemPath) -> Result<()> {
    let (id, params) = connection.initialize_start()?;
    let params: InitializeParams =
        serde_json::from_value(params).context("invalid LSP initialize request")?;
    let encoding = Encoding::negotiate(&params.capabilities);
    let host_settings = match star_host::HostSettings::parse(params.initialization_options) {
        Ok(settings) => settings,
        Err(error) => {
            connection
                .sender
                .send(ServerMessage::Response(Response::new_err(
                    id,
                    ErrorCode::InvalidParams as i32,
                    format!("invalid Sty server configuration: {error:#}"),
                )))?;
            // Respond immediately, then wait for client exit or EOF so the
            // stdio reader ends and the I/O threads can safely be joined.
            while let Ok(message) = connection.receiver.recv() {
                match message {
                    ServerMessage::Notification(notification)
                        if notification.method == ExitNotification::METHOD.as_str() =>
                    {
                        break;
                    }
                    ServerMessage::Request(Request { id, method, .. }) => {
                        let response = if method == ShutdownRequest::METHOD.as_str() {
                            Response::new_ok(id, serde_json::Value::Null)
                        } else {
                            Response::new_err(
                                id,
                                ErrorCode::MethodNotFound as i32,
                                "Sty could not initialize with the supplied hostSources".into(),
                            )
                        };
                        connection.sender.send(ServerMessage::Response(response))?;
                    }
                    _ => {}
                }
            }
            return Ok(());
        }
    };
    let capabilities = ServerCapabilities {
        position_encoding: Some(encoding.kind()),
        completion_provider: Some(lsp_types::CompletionOptions {
            trigger_characters: Some(vec![".".into()]),
            ..lsp_types::CompletionOptions::default()
        }),
        definition_provider: Some(true.into()),
        text_document_sync: Some(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::Incremental),
                ..TextDocumentSyncOptions::default()
            }
            .into(),
        ),
        ..ServerCapabilities::default()
    };
    connection.initialize_finish(
        id,
        serde_json::json!({"capabilities": capabilities, "serverInfo": {"name": "sty"}}),
    )?;

    let system = EditorSystem::new(cwd);
    let db = StyDb::with_system(Arc::new(system.clone()));
    let host = (!host_settings.host_sources.is_empty()).then(star_host::HostWorker::new);
    Server {
        connection,
        db,
        system,
        documents: HashMap::new(),
        published: HashSet::new(),
        published_host: HashSet::new(),
        host_sources: host_settings.host_sources,
        host,
        bazel_analyses: Vec::new(),
        host_analyses: BTreeMap::new(),
        pending: VecDeque::new(),
        encoding,
        revision: 0,
        host_revision: 0,
        shutdown: false,
        needs_bazel_check: false,
        needs_host_check: false,
    }
    .run()
}

impl Server {
    fn editor_request(&mut self, request: Request) -> Response {
        let Request { id, method, params } = request;
        if !matches!(
            method.as_str(),
            "textDocument/completion" | "textDocument/definition"
        ) {
            return Response::new_err(
                id,
                ErrorCode::MethodNotFound as i32,
                format!("Sty does not implement {method}"),
            );
        }
        let result = self.editor_result(&method, params);
        match result {
            Ok(value) => Response::new_ok(id, value),
            Err(error) => {
                Response::new_err(id, ErrorCode::InvalidParams as i32, format!("{error:#}"))
            }
        }
    }

    fn editor_result(
        &mut self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<serde_json::Value> {
        let params: lsp_types::TextDocumentPositionParams = serde_json::from_value(params)?;
        let path = uri_path(&params.text_document.uri)?;
        let text = self
            .system
            .text(&path)
            .ok_or_else(|| anyhow!("request for unopened document {path}"))?;
        let index = LineIndex::from_source_text(&text.text);
        let offset = TextSize::try_from(text_offset(
            &text.text,
            &index,
            params.position,
            self.encoding,
        )?)?;
        // A host graph may still be running or reject an incomplete edit. IDE
        // recovery uses its last attested facts with every current overlay.
        let mut documents: Vec<_> = self.documents.keys().collect();
        documents.sort();
        for analysis in self.host_analyses.values_mut() {
            for open in &documents {
                if let Some(text) = self.system.text(open) {
                    for source in analysis_source_paths(analysis, open) {
                        analysis.update_source(&source, &text.text)?;
                    }
                }
            }
        }
        let mut completions = Vec::new();
        let mut locations = Vec::new();
        for analysis in self
            .bazel_analyses
            .iter()
            .chain(self.host_analyses.values())
        {
            for source in analysis_source_paths(analysis, &path) {
                if method == "textDocument/completion" {
                    for item in analysis.completions(&source, offset) {
                        if !completions.contains(&item) {
                            completions.push(item);
                        }
                    }
                } else {
                    for definition in analysis.definitions(&source, offset) {
                        let span = Span::from(definition.source).with_range(definition.range);
                        if let Some(location) =
                            span_location(&self.db, &self.documents, &span, self.encoding)?
                            && !locations.contains(&location)
                        {
                            locations.push(location);
                        }
                    }
                }
            }
        }
        if method == "textDocument/definition" {
            return Ok(serde_json::to_value(locations)?);
        }
        let items: Vec<_> = completions
            .into_iter()
            .enumerate()
            .map(|(index, item)| lsp_types::CompletionItem {
                label: item.label,
                insert_text: item.insert,
                kind: item.kind.map(completion_kind),
                detail: item.detail,
                documentation: item.documentation.map(lsp_types::Documentation::String),
                sort_text: Some(format!("{index:08}")),
                ..lsp_types::CompletionItem::default()
            })
            .collect();
        Ok(serde_json::to_value(lsp_types::CompletionList {
            is_incomplete: true,
            items,
            ..lsp_types::CompletionList::default()
        })?)
    }

    fn run(mut self) -> Result<()> {
        loop {
            let (message, completed) = if let Some(message) = self.pending.pop_front() {
                (Some(message), None)
            } else if let Some(finished) = self.host.as_ref().map(|host| host.finished.clone()) {
                crossbeam::channel::select! {
                    recv(self.connection.receiver) -> incoming => (incoming.ok(), None),
                    recv(finished) -> result => (None, Some(result.context("Sty host graph worker stopped")?)),
                }
            } else {
                (self.connection.receiver.recv().ok(), None)
            };
            if let Some(completed) = completed {
                self.finish_host(&completed)?;
                if self.needs_bazel_check && !self.shutdown {
                    self.publish_bazel()?;
                }
                if self.needs_host_check && !self.shutdown {
                    self.request_host()?;
                }
                continue;
            }
            let Some(message) = message else {
                return Ok(());
            };
            if self.handle_message(message)? {
                return Ok(());
            }
            self.drain_editor_notifications()?;
            if self.needs_bazel_check {
                self.publish_bazel()?;
            }
            if self.needs_host_check && !self.shutdown {
                self.request_host()?;
            }
        }
    }

    fn handle_message(&mut self, message: ServerMessage) -> Result<bool> {
        match message {
            ServerMessage::Request(request) => {
                let response = if request.method == ShutdownRequest::METHOD.as_str() {
                    self.shutdown = true;
                    Response::new_ok(request.id, serde_json::Value::Null)
                } else if self.shutdown {
                    Response::new_err(
                        request.id,
                        ErrorCode::InvalidRequest as i32,
                        "Sty has shut down".into(),
                    )
                } else {
                    self.editor_request(request)
                };
                self.connection
                    .sender
                    .send(ServerMessage::Response(response))?;
            }
            ServerMessage::Notification(notification) => {
                if notification.method == ExitNotification::METHOD.as_str() {
                    return Ok(true);
                }
                if self.shutdown {
                    return Ok(false);
                }
                self.apply_notification(notification)?;
            }
            ServerMessage::Response(_) => {}
        }
        Ok(false)
    }

    fn handle_notification(&mut self, notification: lsp_server::Notification) -> Result<()> {
        let lsp_server::Notification { method, params } = notification;
        match method.as_str() {
            "textDocument/didOpen" => {
                let params: DidOpenTextDocumentParams = serde_json::from_value(params)?;
                let path = uri_path(&params.text_document.uri)?;
                let revision = self.next_revision();
                self.system.open(
                    path.clone(),
                    OpenText {
                        text: params.text_document.text,
                        revision,
                    },
                );
                File::sync_path(&mut self.db, &path);
                self.needs_bazel_check |= is_bazel_relevant(&path);
                self.mark_host_change(&path);
                self.documents.insert(
                    path,
                    OpenDocument {
                        uri: params.text_document.uri,
                        version: params.text_document.version,
                        revision,
                    },
                );
            }
            "textDocument/didChange" => {
                let params: DidChangeTextDocumentParams = serde_json::from_value(params)?;
                let path = uri_path(&params.text_document.text_document_identifier.uri)?;
                let document = self
                    .documents
                    .get(&path)
                    .ok_or_else(|| anyhow!("change for unopened document {path}"))?;
                if params.text_document.version <= document.version {
                    return Ok(());
                }
                let previous = self
                    .system
                    .text(&path)
                    .ok_or_else(|| anyhow!("change for unopened document {path}"))?;
                let text = apply_changes(previous.text, params.content_changes, self.encoding)?;
                let revision = self.next_revision();
                let document = self
                    .documents
                    .get_mut(&path)
                    .ok_or_else(|| anyhow!("change for unopened document {path}"))?;
                document.version = params.text_document.version;
                document.revision = revision;
                self.system.open(path.clone(), OpenText { text, revision });
                File::sync_path(&mut self.db, &path);
                self.needs_bazel_check |= is_bazel_relevant(&path);
                self.mark_host_change(&path);
            }
            "textDocument/didClose" => {
                let params: DidCloseTextDocumentParams = serde_json::from_value(params)?;
                let path = uri_path(&params.text_document.uri)?;
                if self.is_host_input(&path) {
                    self.invalidate_host();
                }
                self.documents.remove(&path);
                self.system.close(&path);
                File::sync_path(&mut self.db, &path);
                self.needs_bazel_check |= is_bazel_relevant(&path);
            }
            "textDocument/didSave" => {
                let params: DidSaveTextDocumentParams = serde_json::from_value(params)?;
                let path = uri_path(&params.text_document.uri)?;
                File::sync_path(&mut self.db, &path);
                self.needs_bazel_check |= is_bazel_relevant(&path);
                if self.is_host_input(&path) {
                    self.invalidate_host();
                }
            }
            "workspace/didChangeWatchedFiles" => {
                let params: DidChangeWatchedFilesParams = serde_json::from_value(params)?;
                for event in params.changes {
                    let path = uri_path(&event.uri)?;
                    if self.is_host_input(&path) {
                        self.invalidate_host();
                    }
                    File::sync_path(&mut self.db, &path);
                    self.needs_bazel_check |= is_bazel_relevant(&path);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn next_revision(&mut self) -> u64 {
        self.revision += 1;
        self.revision
    }

    fn mark_host_change(&mut self, path: &SystemPath) {
        if self.is_host_input(path) {
            self.host_revision += 1;
            self.needs_host_check = true;
        }
    }

    fn invalidate_host(&mut self) {
        self.host_analyses.clear();
        self.host_revision += 1;
        self.needs_host_check = true;
    }

    fn is_host_input(&self, path: &SystemPath) -> bool {
        path.extension() == Some("star")
            || self.host_sources.iter().any(|source| {
                std::iter::once(&source.checker)
                    .chain(source.runfiles_manifest.iter())
                    .chain(source.inputs.values())
                    .any(|input| {
                        input == path.as_std_path()
                            || input
                                .canonicalize()
                                .ok()
                                .zip(path.as_std_path().canonicalize().ok())
                                .is_some_and(|(left, right)| left == right)
                    })
            })
            || self
                .host_analyses
                .values()
                .any(|analysis| !analysis_source_paths(analysis, path).is_empty())
    }

    fn apply_notification(&mut self, notification: lsp_server::Notification) -> Result<()> {
        let method = notification.method.clone();
        if let Err(error) = self.handle_notification(notification) {
            self.connection.sender.send(ServerMessage::Notification(
                lsp_server::Notification::new(
                    "window/logMessage".into(),
                    serde_json::json!({
                        "type": 1,
                        "message": format!("Sty rejected {method}: {error:#}"),
                    }),
                ),
            ))?;
        }
        Ok(())
    }

    fn drain_editor_notifications(&mut self) -> Result<()> {
        if self.shutdown || !self.pending.is_empty() {
            return Ok(());
        }
        while let Ok(message) = self.connection.receiver.try_recv() {
            match message {
                ServerMessage::Notification(notification)
                    if notification.method != ExitNotification::METHOD.as_str() =>
                {
                    self.apply_notification(notification)?;
                }
                other => {
                    self.pending.push_back(other);
                    break;
                }
            }
        }
        Ok(())
    }

    fn publish_bazel(&mut self) -> Result<()> {
        // Source graph queries share Salsa inputs while every selected graph
        // remains scoped to one marked main repository.
        loop {
            self.needs_bazel_check = false;
            let mut analyses = Vec::new();
            let mut by_uri: HashMap<Uri, Vec<Diagnostic>> = HashMap::new();
            let mut documents: Vec<_> = self.documents.iter().collect();
            documents.sort_by_key(|(path, _)| *path);
            let mut groups: BTreeMap<SystemPathBuf, Vec<BazelSource<'_>>> = BTreeMap::new();
            for (path, document) in documents {
                if !is_bazel_source(path) {
                    continue;
                }
                by_uri.entry(document.uri.clone()).or_default();
                match select_bazel_file(&self.db, path) {
                    Ok((root, source)) => groups.entry(root).or_default().push(source),
                    Err(error) => {
                        by_uri
                            .entry(document.uri.clone())
                            .or_default()
                            .push(setup_diagnostic(format!("{error:#}")));
                        continue;
                    }
                }
            }
            for sources in groups.values() {
                let problems = match analyze_bazel_graph(&self.db, sources) {
                    Ok((diagnostics, analysis)) => {
                        let needs_recovery = analysis.as_ref().is_none_or(|analysis| {
                            sources.iter().any(|source| {
                                source
                                    .selected_file(&self.db)
                                    .path(&self.db)
                                    .as_system_path()
                                    .is_none_or(|path| !analysis.contains(path))
                            })
                        });
                        let analysis = if needs_recovery {
                            recover_bazel_graph(&self.db, sources)
                                .ok()
                                .flatten()
                                .or(analysis)
                        } else {
                            analysis
                        };
                        analyses.extend(analysis);
                        diagnostics
                    }
                    Err(failure) => vec![failure.diagnostic()],
                };
                for problem in problems {
                    let (uri, diagnostic) =
                        lsp_diagnostic(&self.db, &self.documents, &problem, self.encoding)?;
                    let items = by_uri.entry(uri).or_default();
                    if !items.contains(&diagnostic) {
                        items.push(diagnostic);
                    }
                }
            }
            // A newer editor notification may have arrived while a graph was
            // computed. Apply it and recompute before publishing old spans.
            self.drain_editor_notifications()?;
            if self.needs_bazel_check {
                continue;
            }
            self.bazel_analyses = analyses;
            send_publications(
                &self.connection,
                &self.documents,
                &mut self.published,
                by_uri,
            )?;
            return Ok(());
        }
    }

    fn request_host(&mut self) -> Result<()> {
        self.needs_host_check = false;
        let Some(worker) = &self.host else {
            let by_uri = self
                .documents
                .iter()
                .filter(|(path, _)| path.extension() == Some("star"))
                .map(|(_, document)| {
                    (
                        document.uri.clone(),
                        vec![setup_diagnostic(
                            "configure hostSources in Sty server initialization options to check this .star source"
                                .into(),
                        )],
                    )
                })
                .collect();
            return send_publications(
                &self.connection,
                &self.documents,
                &mut self.published_host,
                by_uri,
            );
        };
        let mut overlays = Vec::new();
        let mut versions = Vec::new();
        let mut physical_uris = HashMap::new();
        let mut alias_conflict = None;
        let mut overlay_bytes = 0usize;
        let mut documents: Vec<_> = self.documents.iter().collect();
        documents.sort_by(|(left, _), (right, _)| {
            let is_root = |path: &SystemPathBuf| {
                self.host_sources
                    .iter()
                    .any(|source| source.root == path.as_std_path())
            };
            (!is_root(left), left).cmp(&(!is_root(right), right))
        });
        for (path, document) in documents {
            if path.extension() != Some("star") {
                continue;
            }
            versions.push((path.as_std_path().to_path_buf(), document.version));
            if !path.as_std_path().exists() {
                continue;
            }
            let physical_path = match path.as_std_path().canonicalize() {
                Ok(path) => path,
                Err(error) => {
                    alias_conflict =
                        Some(format!("cannot locate opened host source {path}: {error}"));
                    continue;
                }
            };
            if physical_uris
                .insert(physical_path.clone(), document.uri.clone())
                .is_some()
            {
                alias_conflict = Some(format!(
                    "opened host sources alias the same physical file {}: close one of the duplicate editor paths",
                    physical_path.display()
                ));
            }
            let Some(text) = self.system.text(path) else {
                alias_conflict = Some(format!("opened host source {path} has no editor text"));
                continue;
            };
            if text.text.len() > 2 * 1024 * 1024 {
                // If the host actually loads this opened file, the snapshot
                // attestation below reports the missing overlay as a failure.
                continue;
            }
            let encoded = serde_json::to_vec(&text.text)?;
            let bytes = encoded.len() + physical_path.as_os_str().len() + 32;
            if overlay_bytes.saturating_add(bytes) > 30 * 1024 * 1024 {
                // An actually loaded omitted source fails snapshot attestation.
                continue;
            }
            overlay_bytes += bytes;
            overlays.push(star_host::HostOverlay {
                path: physical_path,
                text: text.text,
            });
        }
        if let Some(error) = alias_conflict {
            self.host_analyses.clear();
            let by_uri = self
                .documents
                .iter()
                .filter(|(path, _)| path.extension() == Some("star"))
                .map(|(_, document)| (document.uri.clone(), vec![setup_diagnostic(error.clone())]))
                .collect();
            return send_publications(
                &self.connection,
                &self.documents,
                &mut self.published_host,
                by_uri,
            );
        }
        worker.request(star_host::HostJob {
            revision: self.host_revision,
            sources: self.host_sources.clone(),
            overlays,
            versions,
        })
    }

    fn finish_host(&mut self, completion: &star_host::HostCompletion) -> Result<()> {
        self.drain_editor_notifications()?;
        if self.shutdown || self.host_revision != completion.job.revision {
            return Ok(());
        }
        for (path, version) in &completion.job.versions {
            let path = SystemPath::new(
                path.to_str()
                    .ok_or_else(|| anyhow!("host editor path is not UTF-8"))?,
            );
            if self
                .documents
                .get(path)
                .is_none_or(|document| document.version != *version)
            {
                return Ok(());
            }
        }
        let checked =
            star_host::check_completion(&self.db, &self.documents, completion, self.encoding);
        self.drain_editor_notifications()?;
        if self.shutdown || self.host_revision != completion.job.revision {
            return Ok(());
        }
        for (root, analysis) in checked.analyses {
            if let Some(analysis) = analysis {
                self.host_analyses.insert(root, analysis);
            } else {
                self.host_analyses.remove(&root);
            }
        }
        send_publications(
            &self.connection,
            &self.documents,
            &mut self.published_host,
            checked.diagnostics,
        )
    }
}

fn analysis_source_paths(analysis: &Analysis, path: &SystemPath) -> Vec<SystemPathBuf> {
    let physical = path.as_std_path().canonicalize().ok();
    let mut paths = Vec::new();
    for source in analysis.source_paths() {
        let matches = source == path
            || physical.as_ref().is_some_and(|physical| {
                source
                    .as_std_path()
                    .canonicalize()
                    .is_ok_and(|source| &source == physical)
            });
        if matches
            && !paths
                .iter()
                .any(|previous: &SystemPathBuf| previous.as_path() == source)
        {
            paths.push(source.to_path_buf());
        }
    }
    paths
}

fn completion_kind(kind: CompletionKind) -> lsp_types::CompletionItemKind {
    match kind {
        CompletionKind::Text => lsp_types::CompletionItemKind::Text,
        CompletionKind::Method => lsp_types::CompletionItemKind::Method,
        CompletionKind::Function => lsp_types::CompletionItemKind::Function,
        CompletionKind::Constructor => lsp_types::CompletionItemKind::Constructor,
        CompletionKind::Field => lsp_types::CompletionItemKind::Field,
        CompletionKind::Variable => lsp_types::CompletionItemKind::Variable,
        CompletionKind::Class => lsp_types::CompletionItemKind::Class,
        CompletionKind::Interface => lsp_types::CompletionItemKind::Interface,
        CompletionKind::Module => lsp_types::CompletionItemKind::Module,
        CompletionKind::Property => lsp_types::CompletionItemKind::Property,
        CompletionKind::Unit => lsp_types::CompletionItemKind::Unit,
        CompletionKind::Value => lsp_types::CompletionItemKind::Value,
        CompletionKind::Enum => lsp_types::CompletionItemKind::Enum,
        CompletionKind::Keyword => lsp_types::CompletionItemKind::Keyword,
        CompletionKind::Snippet => lsp_types::CompletionItemKind::Snippet,
        CompletionKind::Color => lsp_types::CompletionItemKind::Color,
        CompletionKind::File => lsp_types::CompletionItemKind::File,
        CompletionKind::Reference => lsp_types::CompletionItemKind::Reference,
        CompletionKind::Folder => lsp_types::CompletionItemKind::Folder,
        CompletionKind::EnumMember => lsp_types::CompletionItemKind::EnumMember,
        CompletionKind::Constant => lsp_types::CompletionItemKind::Constant,
        CompletionKind::Struct => lsp_types::CompletionItemKind::Struct,
        CompletionKind::Event => lsp_types::CompletionItemKind::Event,
        CompletionKind::Operator => lsp_types::CompletionItemKind::Operator,
        CompletionKind::TypeParameter => lsp_types::CompletionItemKind::TypeParameter,
    }
}

fn send_publications(
    connection: &Connection,
    documents: &HashMap<SystemPathBuf, OpenDocument>,
    published: &mut HashSet<Uri>,
    mut by_uri: HashMap<Uri, Vec<Diagnostic>>,
) -> Result<()> {
    let next: HashSet<Uri> = by_uri.keys().cloned().collect();
    let mut uris: Vec<Uri> = published
        .drain()
        .chain(next.iter().cloned())
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();
    uris.sort_by(|left, right| left.as_str().cmp(right.as_str()));
    for uri in uris {
        let version = documents
            .values()
            .find(|document| document.uri == uri)
            .map(|document| document.version);
        connection
            .sender
            .send(ServerMessage::Notification(lsp_server::Notification::new(
                PublishDiagnosticsNotification::METHOD.into(),
                PublishDiagnosticsParams {
                    uri: uri.clone(),
                    diagnostics: by_uri.remove(&uri).unwrap_or_default(),
                    version,
                },
            )))?;
    }
    *published = next;
    Ok(())
}

fn is_bazel_source(path: &SystemPath) -> bool {
    matches!(path.file_name(), Some("BUILD" | "BUILD.bazel"))
        || path.extension() == Some("bzl")
        || path.as_str().ends_with(".bzl.pyi")
}

fn is_bazel_relevant(path: &SystemPath) -> bool {
    is_bazel_source(path)
        || matches!(
            path.file_name(),
            Some(
                "BUILD"
                    | "BUILD.bazel"
                    | "MODULE.bazel"
                    | "REPO.bazel"
                    | "WORKSPACE"
                    | "WORKSPACE.bazel"
            )
        )
}

fn select_bazel_file<'db>(
    db: &'db StyDb,
    path: &SystemPath,
) -> Result<(SystemPathBuf, BazelSource<'db>)> {
    let source = if path.as_str().ends_with(".bzl.pyi") {
        let source = path
            .as_str()
            .strip_suffix(".pyi")
            .ok_or_else(|| anyhow!("invalid Bazel stub path {path}"))?;
        SystemPath::new(source)
    } else {
        path
    };
    let directory = source
        .parent()
        .ok_or_else(|| anyhow!("Bazel source has no parent directory: {path}"))?;
    let root = find_bazel_repository(db, directory)
        .ok_or_else(|| anyhow!("no Bazel repository marker above {path}"))?;
    db.files().try_add_root(db, &root, FileRootKind::Project);
    let file = system_path_to_file(db, source)
        .with_context(|| format!("cannot select Bazel source {source}"))?;
    Ok((
        root.clone(),
        BazelSource::new(db, BazelRepository::new(db, root), file),
    ))
}

fn uri_path(uri: &Uri) -> Result<SystemPathBuf> {
    let path = uri
        .to_file_path()
        .map_err(|()| anyhow!("Sty checks only file URIs: {uri}"))?;
    SystemPathBuf::from_path_buf(path)
        .map_err(|path| anyhow!("Sty source path is not UTF-8: {path:?}"))
}

fn file_uri(
    db: &StyDb,
    file: File,
    documents: &HashMap<SystemPathBuf, OpenDocument>,
) -> Result<Uri> {
    let path = file
        .path(db)
        .as_system_path()
        .ok_or_else(|| anyhow!("Sty problem has no source path"))?;
    if let Some(document) = documents.get(path) {
        return Ok(document.uri.clone());
    }
    Uri::from_file_path(path.as_std_path())
        .map_err(|()| anyhow!("cannot represent Sty source URI {path}"))
}

fn setup_diagnostic(message: String) -> Diagnostic {
    Diagnostic {
        range: Range::new(Position::new(0, 0), Position::new(0, 0)),
        severity: Some(DiagnosticSeverity::Error),
        source: Some("sty".into()),
        message: lsp_types::Message::String(message),
        ..Diagnostic::default()
    }
}

/// Project shared diagnostics, including declaration locations and nested notes.
fn lsp_diagnostic(
    db: &StyDb,
    documents: &HashMap<SystemPathBuf, OpenDocument>,
    diagnostic: &SourceDiagnostic,
    encoding: Encoding,
) -> Result<(Uri, Diagnostic)> {
    let primary = diagnostic
        .primary_span()
        .ok_or_else(|| anyhow!("Sty diagnostic has no source"))?;
    let location = span_location(db, documents, &primary, encoding)?
        .ok_or_else(|| anyhow!("Sty diagnostic has no navigable primary source"))?;
    let mut message = diagnostic.concise_message().to_string();
    let mut related = Vec::new();
    let mut append = |span: Option<&Span>, text: String| -> Result<()> {
        let location = match span {
            Some(span) => span_location(db, documents, span, encoding)?,
            None => None,
        };
        if let Some(location) = location {
            related.push(DiagnosticRelatedInformation {
                location,
                message: text,
            });
        } else {
            write!(message, "\n\n{text}")?;
            if let Some(span) = span
                && let UnifiedFile::Ruff(source) = span.file()
            {
                write!(message, " ({name}", name = source.name())?;
                if let Some(range) = span.range() {
                    let position = source_position(
                        source.source_text(),
                        source.index(),
                        range.start(),
                        encoding,
                    )?;
                    write!(message, ":{}", position.line + 1)?;
                }
                message.push(')');
            }
        }
        Ok(())
    };
    for annotation in diagnostic.secondary_annotations() {
        if let Some(text) = annotation.get_message() {
            append(Some(annotation.get_span()), text.to_string())?;
        }
    }
    for sub in diagnostic.sub_diagnostics() {
        append(
            sub.primary_span_ref(),
            format!("{}: {}", sub.severity(), sub.concise_message()),
        )?;
        for annotation in sub.secondary_annotations() {
            if let Some(text) = annotation.get_message() {
                append(Some(annotation.get_span()), text.to_string())?;
            }
        }
    }
    let severity = match diagnostic.severity() {
        Severity::Info => DiagnosticSeverity::Information,
        Severity::Warning => DiagnosticSeverity::Warning,
        Severity::Error => DiagnosticSeverity::Error,
        Severity::Fatal => DiagnosticSeverity::Error,
    };
    Ok((
        location.uri,
        Diagnostic {
            range: location.range,
            severity: Some(severity),
            code: Some(lsp_types::Code::String(diagnostic.id().to_string())),
            source: Some("sty".into()),
            message: lsp_types::Message::String(message),
            related_information: (!related.is_empty()).then_some(related),
            ..Diagnostic::default()
        },
    ))
}

fn span_location(
    db: &StyDb,
    documents: &HashMap<SystemPathBuf, OpenDocument>,
    span: &Span,
    encoding: Encoding,
) -> Result<Option<Location>> {
    let (uri, range) = match span.file() {
        UnifiedFile::Ty(file) => {
            let uri = file_uri(db, *file, documents)?;
            let range = if let Some(range) = span.range() {
                let source = source_text(db, *file);
                let index = line_index(db, *file);
                text_range(source.as_str(), &index, range, encoding)?
            } else {
                Range::default()
            };
            (uri, range)
        }
        UnifiedFile::Ruff(source) => {
            let path = SystemPath::new(source.name());
            if !path.is_absolute() {
                if let Some(range) = span.range() {
                    text_range(source.source_text(), source.index(), range, encoding)?;
                }
                return Ok(None);
            }
            let document = documents.get(path).or_else(|| {
                let physical = path.as_std_path().canonicalize().ok()?;
                documents.iter().find_map(|(path, document)| {
                    path.as_std_path()
                        .canonicalize()
                        .ok()
                        .filter(|path| path == &physical)
                        .map(|_| document)
                })
            });
            let uri = if let Some(document) = document {
                document.uri.clone()
            } else {
                Uri::from_file_path(path.as_std_path())
                    .map_err(|()| anyhow!("cannot represent Sty source URI {path}"))?
            };
            let range = if let Some(range) = span.range() {
                text_range(source.source_text(), source.index(), range, encoding)?
            } else {
                Range::default()
            };
            (uri, range)
        }
    };
    Ok(Some(Location { uri, range }))
}

fn text_range(
    text: &str,
    index: &LineIndex,
    range: TextRange,
    encoding: Encoding,
) -> Result<Range> {
    let bytes = range.start().to_usize()..range.end().to_usize();
    if text.get(bytes).is_none() {
        return Err(anyhow!("Sty diagnostic span is outside its source"));
    }
    Ok(Range::new(
        source_position(text, index, range.start(), encoding)?,
        source_position(text, index, range.end(), encoding)?,
    ))
}

fn source_position(
    text: &str,
    index: &LineIndex,
    offset: TextSize,
    encoding: Encoding,
) -> Result<Position> {
    let location = index.source_location(offset, text, encoding.source());
    let line = u32::try_from(location.line.to_zero_indexed())?;
    let character = u32::try_from(location.character_offset.to_zero_indexed())?;
    Ok(Position::new(line, character))
}

fn text_offset(
    text: &str,
    index: &LineIndex,
    position: Position,
    encoding: Encoding,
) -> Result<usize> {
    let line = usize::try_from(position.line)?;
    let character = usize::try_from(position.character)?;
    let offset = index.offset(
        SourceLocation {
            line: OneIndexed::from_zero_indexed(line),
            character_offset: OneIndexed::from_zero_indexed(character),
        },
        text,
        encoding.source(),
    );
    let offset = offset.to_usize();
    if !text.is_char_boundary(offset) {
        return Err(anyhow!("editor change splits a UTF-8 character"));
    }
    Ok(offset)
}

fn apply_changes(
    mut text: String,
    changes: Vec<TextDocumentContentChangeEvent>,
    encoding: Encoding,
) -> Result<String> {
    for change in changes {
        match change {
            TextDocumentContentChangeEvent::TextDocumentContentChangeWholeDocument(
                TextDocumentContentChangeWholeDocument { text: new_text },
            ) => text = new_text,
            TextDocumentContentChangeEvent::TextDocumentContentChangePartial(
                TextDocumentContentChangePartial {
                    range,
                    text: replacement,
                    ..
                },
            ) => {
                let index = LineIndex::from_source_text(&text);
                let start = text_offset(&text, &index, range.start, encoding)?;
                let end = text_offset(&text, &index, range.end, encoding)?;
                if start > end {
                    return Err(anyhow!("editor change has an inverted source range"));
                }
                text.replace_range(start..end, &replacement);
            }
        }
    }
    Ok(text)
}
