//! Run a host's private loader outside the editor loop and check its captured
//! source graph with Sty. The host owns load resolution and native facts;
//! Sty owns static analysis and every diagnostic.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow};
use crossbeam::channel::{self, Receiver, Sender, TrySendError};
use lsp_types::{Diagnostic, Uri};
use ruff_db::system::SystemPath;
use serde::Deserialize;
use ty_starlark::star::check_star_graph;

use crate::StyDb;
use crate::diagnostics::star_diagnostics;
use crate::host::CapturedGraph;

use super::{Encoding, OpenDocument, lsp_diagnostic, setup_diagnostic};

const GRAPH_LIMIT: usize = 64 * 1024 * 1024;
const STDERR_LIMIT: usize = 1024 * 1024;

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct HostSource {
    pub root: PathBuf,
    pub checker: PathBuf,
    #[serde(default)]
    pub inputs: BTreeMap<String, PathBuf>,
    pub runfiles_manifest: Option<PathBuf>,
}

#[derive(Default, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct HostSettings {
    #[serde(default)]
    pub host_sources: Vec<HostSource>,
}

impl HostSettings {
    pub(super) fn parse(options: Option<serde_json::Value>) -> Result<Self> {
        let settings: Self = match options {
            Some(options) => serde_json::from_value(options)
                .context("invalid Sty hostSources initialization options")?,
            None => Self::default(),
        };
        for source in &settings.host_sources {
            for (name, path) in std::iter::once(("root", &source.root))
                .chain(std::iter::once(("checker", &source.checker)))
                .chain(
                    source
                        .runfiles_manifest
                        .as_ref()
                        .map(|path| ("runfilesManifest", path)),
                )
                .chain(
                    source
                        .inputs
                        .iter()
                        .map(|(name, path)| (name.as_str(), path)),
                )
            {
                if !path.is_absolute() || path.to_str().is_none() {
                    return Err(anyhow!(
                        "hostSources {name} must be an absolute UTF-8 path: {path:?}"
                    ));
                }
            }
            if source
                .root
                .extension()
                .is_none_or(|extension| extension != "star")
            {
                return Err(anyhow!(
                    "hostSources root must be a .star path: {:?}",
                    source.root
                ));
            }
        }
        Ok(settings)
    }
}

#[derive(Clone)]
pub(super) struct HostOverlay {
    pub path: PathBuf,
    pub text: String,
}

pub(super) struct HostJob {
    pub revision: u64,
    pub sources: Vec<HostSource>,
    pub overlays: Vec<HostOverlay>,
    pub versions: Vec<(PathBuf, i32)>,
}

pub(super) struct HostCompletion {
    pub job: HostJob,
    pub outputs: Vec<(HostSource, Result<Vec<u8>, String>)>,
}

pub(super) struct HostWorker {
    sender: Option<Sender<HostJob>>,
    pending: Receiver<HostJob>,
    pub finished: Receiver<HostCompletion>,
    cancel: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
}

impl HostWorker {
    pub(super) fn new() -> Self {
        // One host process can run while only the newest editor snapshot waits.
        let (sender, requests) = channel::bounded::<HostJob>(1);
        let pending = requests.clone();
        let (completed, finished) = channel::bounded(1);
        let cancel = Arc::new(AtomicBool::new(false));
        let worker_cancel = Arc::clone(&cancel);
        let replace_finished = finished.clone();
        let thread = thread::spawn(move || {
            while let Ok(mut job) = requests.recv() {
                if worker_cancel.load(Ordering::Relaxed) {
                    break;
                }
                while let Ok(latest) = requests.try_recv() {
                    job = latest;
                }
                let mut outputs = Vec::new();
                loop {
                    if worker_cancel.load(Ordering::Relaxed) {
                        break;
                    }
                    if let Ok(latest) = requests.try_recv() {
                        job = latest;
                        while let Ok(newer) = requests.try_recv() {
                            job = newer;
                        }
                        outputs.clear();
                    }
                    let Some(source) = job.sources.get(outputs.len()).cloned() else {
                        break;
                    };
                    outputs.push((
                        source.clone(),
                        run_host_graph(
                            &source,
                            &job.overlays,
                            &worker_cancel,
                            Duration::from_secs(30),
                        ),
                    ));
                }
                if worker_cancel.load(Ordering::Relaxed) {
                    break;
                }
                let completion = HostCompletion { job, outputs };
                match completed.try_send(completion) {
                    Ok(()) => {}
                    Err(TrySendError::Full(latest)) => {
                        // The editor has not handled the previous result yet.
                        // Its revision gate also rejects stale results.
                        let _ = replace_finished.try_recv();
                        if completed.try_send(latest).is_err() {
                            break;
                        }
                    }
                    Err(TrySendError::Disconnected(_)) => break,
                }
            }
        });
        Self {
            sender: Some(sender),
            pending,
            finished,
            cancel,
            thread: Some(thread),
        }
    }

    pub(super) fn request(&self, job: HostJob) -> Result<()> {
        let sender = self
            .sender
            .as_ref()
            .ok_or_else(|| anyhow!("Sty host graph worker stopped"))?;
        match sender.try_send(job) {
            Ok(()) => Ok(()),
            Err(TrySendError::Full(latest)) => {
                let _ = self.pending.try_recv();
                sender
                    .try_send(latest)
                    .map_err(|_| anyhow!("Sty host graph worker stopped"))
            }
            Err(TrySendError::Disconnected(_)) => Err(anyhow!("Sty host graph worker stopped")),
        }
    }
}

impl Drop for HostWorker {
    fn drop(&mut self) {
        self.cancel.store(true, Ordering::Relaxed);
        self.sender.take();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn run_host_graph(
    source: &HostSource,
    overlays: &[HostOverlay],
    cancel: &AtomicBool,
    timeout: Duration,
) -> Result<Vec<u8>, String> {
    fn run(
        source: &HostSource,
        overlays: &[HostOverlay],
        cancel: &AtomicBool,
        timeout: Duration,
    ) -> Result<Vec<u8>> {
        let sources: Vec<_> = overlays
            .iter()
            .map(|overlay| serde_json::json!({"path": overlay.path, "source": overlay.text}))
            .collect();
        let bytes = serde_json::to_vec(&serde_json::json!({
            "version": "sty-star-overlays-v1",
            "sources": sources,
        }))?;
        let mut command = Command::new(&source.checker);
        command
            .arg("--sty-graph-v3")
            .arg("--source")
            .arg(&source.root)
            .arg("--sty-overlays-stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for (name, path) in &source.inputs {
            command
                .arg("--input")
                .arg(format!("{name}={}", path.display()));
        }
        if let Some(manifest) = &source.runfiles_manifest {
            command.env("RUNFILES_MANIFEST_FILE", manifest);
        }
        let mut child = command.spawn().with_context(|| {
            format!(
                "cannot start host graph producer {}",
                source.checker.display()
            )
        })?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow!("host graph producer has no stdin"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| anyhow!("host graph producer has no stdout"))?;
        let stderr = child
            .stderr
            .take()
            .ok_or_else(|| anyhow!("host graph producer has no stderr"))?;
        // Drain both output pipes while sending input so either side can
        // consume large graphs without blocking the editor's worker.
        let writer = thread::spawn(move || {
            let mut stdin = stdin;
            stdin.write_all(&bytes)
        });
        let overflow = Arc::new(AtomicBool::new(false));
        let graph_overflow = Arc::clone(&overflow);
        let reader = thread::spawn(move || {
            let mut bytes = Vec::new();
            stdout
                .take((GRAPH_LIMIT + 1) as u64)
                .read_to_end(&mut bytes)?;
            if bytes.len() > GRAPH_LIMIT {
                graph_overflow.store(true, Ordering::Relaxed);
            }
            Ok::<_, std::io::Error>(bytes)
        });
        let stderr_overflow = Arc::clone(&overflow);
        let error_reader = thread::spawn(move || {
            let mut bytes = Vec::new();
            stderr
                .take((STDERR_LIMIT + 1) as u64)
                .read_to_end(&mut bytes)?;
            if bytes.len() > STDERR_LIMIT {
                stderr_overflow.store(true, Ordering::Relaxed);
            }
            Ok::<_, std::io::Error>(bytes)
        });
        let deadline = Instant::now() + timeout;
        let mut status = None;
        let status = loop {
            if overflow.load(Ordering::Relaxed) {
                let _ = child.kill();
                child
                    .wait()
                    .context("cannot reap oversized host graph producer")?;
                drop((writer, reader, error_reader));
                return Err(anyhow!(
                    "host graph producer {} exceeded the 64 MiB graph or 1 MiB stderr output limit",
                    source.checker.display()
                ));
            }
            if cancel.load(Ordering::Relaxed) || Instant::now() >= deadline {
                let reason = if cancel.load(Ordering::Relaxed) {
                    "cancelled on Sty server exit"
                } else {
                    "exceeded the 30 second host graph deadline"
                };
                let _ = child.kill();
                child
                    .wait()
                    .context("cannot reap stopped host graph producer")?;
                // A producer's own children could inherit a pipe after its
                // death; leave I/O readers detached on this failure path.
                drop((writer, reader, error_reader));
                return Err(anyhow!(
                    "host graph producer {} {reason}",
                    source.checker.display()
                ));
            }
            if status.is_none() {
                status = child
                    .try_wait()
                    .context("cannot poll host graph producer")?;
            }
            if let Some(status) = status {
                if writer.is_finished() && reader.is_finished() && error_reader.is_finished() {
                    break status;
                }
            }
            thread::sleep(Duration::from_millis(20));
        };
        let write_error = writer
            .join()
            .map_err(|_| anyhow!("host graph input writer panicked"))?
            .err();
        let stdout = reader
            .join()
            .map_err(|_| anyhow!("host graph output reader panicked"))?
            .context("cannot read host graph output")?;
        let stderr = error_reader
            .join()
            .map_err(|_| anyhow!("host graph error reader panicked"))?
            .context("cannot read host graph stderr")?;
        if !status.success() {
            let stderr = String::from_utf8_lossy(&stderr);
            return Err(anyhow!(
                "host graph producer {} exited {}: {}",
                source.checker.display(),
                status,
                stderr.trim()
            ));
        }
        if let Some(error) = write_error {
            return Err(anyhow!(
                "cannot send unsaved sources to host graph producer: {error}"
            ));
        }
        Ok(stdout)
    }
    run(source, overlays, cancel, timeout).map_err(|error| format!("{error:#}"))
}

pub(super) fn check_completion(
    db: &StyDb,
    documents: &HashMap<ruff_db::system::SystemPathBuf, OpenDocument>,
    completion: &HostCompletion,
    encoding: Encoding,
) -> HashMap<Uri, Vec<Diagnostic>> {
    let mut diagnostics: HashMap<Uri, Vec<Diagnostic>> = HashMap::new();
    let mut visited = HashSet::new();
    let open: HashMap<_, _> = documents
        .iter()
        .filter_map(|(path, document)| {
            canonical(path.as_std_path())
                .ok()
                .map(|path| (path, document))
        })
        .collect();
    let overlays: HashMap<_, _> = completion
        .job
        .overlays
        .iter()
        .filter_map(|overlay| {
            canonical(&overlay.path)
                .ok()
                .map(|path| (path, overlay.text.as_str()))
        })
        .collect();
    let mut host_failure = None;
    let mut failed_roots = HashSet::new();
    for (source, output) in &completion.outputs {
        let root_uri = open
            .get(&canonical(&source.root).unwrap_or_else(|_| source.root.clone()))
            .map_or_else(
                || Uri::from_file_path(&source.root),
                |document| Ok(document.uri.clone()),
            );
        let Ok(root_uri) = root_uri else {
            continue;
        };
        let result = output.as_ref().map_err(|error| anyhow!("{error}"));
        let result = result.and_then(|bytes| {
            let captured: CapturedGraph = serde_json::from_slice(bytes)
                .context("host graph returned invalid versioned JSON")?;
            let mut observed = HashSet::new();
            for (path, text) in captured.sources() {
                let path = canonical(Path::new(path))
                    .with_context(|| format!("cannot locate captured host source {path}"))?;
                if open.contains_key(&path) {
                    let frozen = overlays.get(&path).ok_or_else(|| {
                        anyhow!(
                            "opened host source {} has no frozen editor overlay",
                            path.display()
                        )
                    })?;
                    if frozen != &text {
                        return Err(anyhow!(
                            "host graph snapshot differs from the frozen editor text in {}",
                            path.display()
                        ));
                    }
                }
                observed.insert(path);
            }
            let selected = source
                .root
                .to_str()
                .ok_or_else(|| anyhow!("invalid host root path"))?;
            let graph = captured.into_star_graph(db, SystemPath::new(selected))?;
            let result = check_star_graph(db, &graph)?;
            let problems = star_diagnostics(db, &graph, &result)?;
            let mut graph_diagnostics: HashMap<Uri, Vec<Diagnostic>> = HashMap::new();
            for problem in &problems {
                let (uri, diagnostic) = lsp_diagnostic(db, documents, problem, encoding)?;
                graph_diagnostics.entry(uri).or_default().push(diagnostic);
            }
            Ok((observed, graph_diagnostics))
        });
        match result {
            Ok((observed, mut graph_diagnostics)) => {
                visited.extend(observed);
                let mut uris: Vec<_> = graph_diagnostics.keys().cloned().collect();
                uris.sort_by(|left, right| left.as_str().cmp(right.as_str()));
                for uri in uris {
                    if let Some(items) = graph_diagnostics.remove(&uri) {
                        diagnostics.entry(uri).or_default().extend(items);
                    }
                }
            }
            Err(error) => {
                let failure: String = format!("{error:#}").chars().take(2048).collect();
                host_failure.get_or_insert_with(|| format!("{}: {failure}", source.root.display()));
                failed_roots.insert(root_uri.clone());
                diagnostics
                    .entry(root_uri)
                    .or_default()
                    .push(setup_diagnostic(failure));
            }
        }
    }
    let mut open_documents: Vec<_> = documents.iter().collect();
    open_documents.sort_by_key(|(path, _)| *path);
    for (path, document) in open_documents {
        if path.extension() != Some("star") {
            continue;
        }
        let uri = document.uri.clone();
        diagnostics.entry(uri.clone()).or_default();
        let covered = canonical(path.as_std_path()).is_ok_and(|path| visited.contains(&path));
        if !covered && !failed_roots.contains(&uri) {
            diagnostics.entry(uri).or_default().push(setup_diagnostic(
                if path.as_std_path().exists() {
                    if let Some(failure) = &host_failure {
                        format!("a configured host graph failed before this .star source could be checked: {failure}")
                    } else {
                        "configured host roots did not load this .star source; configure its hostSources root".into()
                    }
                } else {
                    "the host loader needs this .star source to exist on disk before checking unsaved edits"
                        .into()
                },
            ));
        }
    }
    diagnostics
}

fn canonical(path: &Path) -> Result<PathBuf> {
    path.canonicalize()
        .with_context(|| format!("cannot find physical host source {}", path.display()))
}

#[cfg(all(test, unix))]
mod tests {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    use super::*;

    fn checker(script: &str) -> (tempfile::TempDir, HostSource) {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().join("root.star");
        fs::write(&root, "GOOD = 1\n").unwrap();
        let executable = directory.path().join("checker");
        fs::write(&executable, script).unwrap();
        let mut permissions = fs::metadata(&executable).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&executable, permissions).unwrap();
        (
            directory,
            HostSource {
                root,
                checker: executable,
                inputs: BTreeMap::new(),
                runfiles_manifest: None,
            },
        )
    }

    #[test]
    fn producer_that_exits_with_inherited_open_pipes_obeys_cancellation() {
        let (directory, mut source) = checker(concat!(
            "#!/bin/sh\n",
            "for input in \"$@\"; do\n",
            "  case \"$input\" in\n",
            "    release=*) RELEASE=\"${input#release=}\";;\n",
            "    parent=*) PARENT=\"${input#parent=}\";;\n",
            "  esac\n",
            "done\n",
            "( printf 'started' > \"$RELEASE.started\";",
            " while [ ! -e \"$RELEASE\" ]; do sleep 0.01; done;",
            " printf 'done' > \"$RELEASE.done\" ) &\n",
            "printf '%s' \"$$\" > \"$PARENT\"\n",
            "exit 0\n",
        ));
        let release = directory.path().join("release");
        let parent = directory.path().join("parent");
        source.inputs.insert("release".into(), release.clone());
        source.inputs.insert("parent".into(), parent.clone());
        let cancelled = Arc::new(AtomicBool::new(false));
        let worker_cancel = Arc::clone(&cancelled);
        let process = thread::spawn(move || {
            run_host_graph(&source, &[], &worker_cancel, Duration::from_secs(30))
        });
        let deadline = Instant::now() + Duration::from_secs(5);
        while (!release.with_extension("started").exists() || !parent.exists())
            && Instant::now() < deadline
        {
            thread::sleep(Duration::from_millis(20));
        }
        let child_started = release.with_extension("started").exists() && parent.exists();
        let mut wrapper_exited = false;
        if child_started {
            let pid = fs::read_to_string(parent).unwrap();
            while Instant::now() < deadline {
                if !Command::new("kill")
                    .arg("-0")
                    .arg(&pid)
                    .stderr(Stdio::null())
                    .status()
                    .unwrap()
                    .success()
                {
                    wrapper_exited = true;
                    break;
                }
                thread::sleep(Duration::from_millis(20));
            }
        }
        cancelled.store(true, Ordering::Relaxed);
        let result = process.join().unwrap();
        fs::write(&release, "released").unwrap();
        let release_deadline = Instant::now() + Duration::from_secs(5);
        while child_started
            && !release.with_extension("done").exists()
            && Instant::now() < release_deadline
        {
            thread::sleep(Duration::from_millis(20));
        }
        assert!(child_started, "wrapper never started: {result:?}");
        assert!(
            wrapper_exited,
            "wrapper never exited before cancellation: {result:?}"
        );
        assert!(
            release.with_extension("done").exists(),
            "wrapper child did not exit"
        );
        // The completion marker is written just before the descendant closes
        // its inherited output pipes.
        thread::sleep(Duration::from_millis(40));
        let error = result.unwrap_err();
        assert!(error.contains("cancelled on Sty server exit"), "{error}");
    }

    #[test]
    fn overflowing_stderr_is_stopped_without_unbounded_memory_growth() {
        let (_directory, source) =
            checker("#!/bin/sh\ndd if=/dev/zero bs=1048576 count=2 1>&2 2>/dev/null\n");
        let cancelled = AtomicBool::new(false);
        let error = run_host_graph(&source, &[], &cancelled, Duration::from_secs(10)).unwrap_err();
        assert!(error.contains("output limit"), "{error}");
    }

    #[test]
    fn worker_drop_cancels_and_reaps_a_running_host_child() {
        let (directory, mut source) = checker(concat!(
            "#!/bin/sh\n",
            "for input in \"$@\"; do\n",
            "  case \"$input\" in started=*) STARTED=\"${input#started=}\";; esac\n",
            "done\n",
            "printf '%s' \"$$\" > \"$STARTED\"\n",
            "exec sleep 30\n",
        ));
        let started = directory.path().join("started");
        source.inputs.insert("started".into(), started.clone());
        let worker = HostWorker::new();
        worker
            .request(HostJob {
                revision: 1,
                sources: vec![source],
                overlays: vec![],
                versions: vec![],
            })
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while fs::read_to_string(&started)
            .ok()
            .is_none_or(|pid| pid.parse::<u32>().is_err())
            && Instant::now() < deadline
        {
            thread::sleep(Duration::from_millis(20));
        }
        let pid = fs::read_to_string(started).expect("producer did not begin");
        assert!(pid.parse::<u32>().is_ok(), "producer marker has no PID");
        let shutdown = Instant::now();
        drop(worker);
        assert!(shutdown.elapsed() < Duration::from_secs(3));
        assert!(
            !Command::new("kill")
                .arg("-0")
                .arg(pid)
                .stderr(Stdio::null())
                .status()
                .unwrap()
                .success(),
            "a stopped host process remained alive"
        );
    }
}
