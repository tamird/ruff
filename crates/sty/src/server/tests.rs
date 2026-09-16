use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicI32, Ordering};
use std::thread::{self, JoinHandle};
use std::time::Duration;

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
#[cfg(unix)]
use std::os::unix::fs::symlink;

use lsp_server::{Connection, Message, Notification, Request, RequestId};
use lsp_types::{Diagnostic, PublishDiagnosticsParams, Uri};

use super::{Encoding, apply_changes, run_connection};

struct TestServer {
    root: tempfile::TempDir,
    connection: Connection,
    thread: Option<JoinHandle<()>>,
    request_id: AtomicI32,
}

impl TestServer {
    fn new() -> Self {
        Self::with_options(|_| serde_json::json!({}))
    }

    fn with_options(options: impl FnOnce(&Path) -> serde_json::Value) -> Self {
        let root = tempfile::tempdir().unwrap();
        let settings = options(root.path());
        let path = root.path().to_str().unwrap().to_owned();
        let (server, connection) = Connection::memory();
        let thread = thread::spawn(move || {
            run_connection(server, ruff_db::system::SystemPath::new(&path)).unwrap();
        });
        let harness = Self {
            root,
            connection,
            thread: Some(thread),
            request_id: AtomicI32::new(10),
        };
        harness
            .connection
            .sender
            .send(Message::Request(Request {
                id: RequestId::from(1),
                method: "initialize".into(),
                params: serde_json::json!({"capabilities": {}, "initializationOptions": settings}),
            }))
            .unwrap();
        let response = harness
            .connection
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .unwrap();
        let Message::Response(response) = response else {
            panic!("expected initialize response, got {response:?}");
        };
        assert!(response.response_result.is_ok(), "{response:?}");
        assert_eq!(
            response.response_result.as_ref().unwrap()["capabilities"]["positionEncoding"],
            "utf-16"
        );
        harness.notify("initialized", serde_json::json!({}));
        harness
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.path().join(relative)
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self.path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn uri(&self, relative: &str) -> Uri {
        Uri::from_file_path(self.path(relative)).unwrap()
    }

    fn notify(&self, method: &str, params: serde_json::Value) {
        self.connection
            .sender
            .send(Message::Notification(Notification {
                method: method.into(),
                params,
            }))
            .unwrap();
    }

    fn open(&self, relative: &str, text: &str, version: i32) {
        self.notify(
            "textDocument/didOpen",
            serde_json::json!({
                "textDocument": {"uri":self.uri(relative),"languageId":"starlark", "version":version,"text":text}
            }),
        );
    }

    fn change(&self, relative: &str, version: i32, content_changes: &serde_json::Value) {
        self.notify(
            "textDocument/didChange",
            serde_json::json!({
                "textDocument":{"uri":self.uri(relative),"version":version},
                "contentChanges":content_changes
            }),
        );
    }

    fn close(&self, relative: &str) {
        self.notify(
            "textDocument/didClose",
            serde_json::json!({"textDocument":{"uri":self.uri(relative)}}),
        );
    }

    fn published(&self, relative: &str) -> PublishDiagnosticsParams {
        self.published_uri(&self.uri(relative))
    }

    fn published_uri(&self, uri: &Uri) -> PublishDiagnosticsParams {
        for _ in 0..16 {
            let message = self
                .connection
                .receiver
                .recv_timeout(Duration::from_secs(5))
                .unwrap();
            let Message::Notification(notification) = message else {
                panic!("unexpected server message {message:?}");
            };
            assert_eq!(notification.method, "textDocument/publishDiagnostics");
            let publication: PublishDiagnosticsParams =
                serde_json::from_value(notification.params).unwrap();
            if &publication.uri == uri {
                return publication;
            }
        }
        panic!("no diagnostics for {uri}");
    }

    fn logged_error(&self, expected: &str) {
        let message = self
            .connection
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .unwrap();
        let Message::Notification(notification) = message else {
            panic!("expected editor log message, got {message:?}");
        };
        assert_eq!(notification.method, "window/logMessage");
        assert_eq!(notification.params["type"], 1);
        assert!(
            notification.params["message"]
                .as_str()
                .unwrap()
                .contains(expected)
        );
    }

    fn no_pending_publication(&self) {
        let id = RequestId::from(self.request_id.fetch_add(1, Ordering::Relaxed));
        self.connection
            .sender
            .send(Message::Request(Request {
                id: id.clone(),
                method: "sty/test/barrier".into(),
                params: serde_json::Value::Null,
            }))
            .unwrap();
        let message = self
            .connection
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .unwrap();
        let Message::Response(response) = message else {
            panic!("unexpected diagnostic publication before the protocol barrier: {message:?}");
        };
        assert_eq!(response.id, id);
        assert!(response.response_result.is_err());
    }
}

impl Drop for TestServer {
    fn drop(&mut self) {
        let _ = self
            .connection
            .sender
            .send(Message::Notification(Notification {
                method: "exit".into(),
                params: serde_json::Value::Null,
            }));
        if let Some(thread) = self.thread.take() {
            if let Err(error) = thread.join() {
                if !thread::panicking() {
                    std::panic::resume_unwind(error);
                }
            }
        }
    }
}

fn has_error(diagnostics: &[Diagnostic], message: &str) -> bool {
    diagnostics.iter().any(
        |item| matches!(&item.message, lsp_types::Message::String(text) if text.contains(message)),
    )
}

#[test]
fn unconfigured_star_open_reports_missing_host_setup() {
    let server = TestServer::new();
    server.write("deploy.star", "GOOD = 1\n");
    server.open("deploy.star", "GOOD = 1\n", 7);
    let result = server.published("deploy.star");
    assert_eq!(result.version, Some(7));
    assert!(
        has_error(&result.diagnostics, "configure hostSources"),
        "{result:?}"
    );
}

#[cfg(unix)]
#[test]
fn configured_star_checks_frozen_root_and_loaded_editor_sources() {
    let server = TestServer::with_options(host_settings);
    let root_source = concat!(
        "load(\"//example:limits.star\", \"LimitConfig\")\n",
        "if False:\n",
        "    LimitConfig(max_connections=\"😀\")\n",
        "    example_host_native(1)\n",
    );
    let declaration = "def validate(value):\n    pass\nLimitConfig = wrapper_record(validate, max_connections=int)\n";
    let loaded_source = format!("{declaration}LimitConfig(max_connections=\"wrong\")\n");
    server.write("root.star", "GOOD = 1\n");
    server.write("limits.star", declaration);
    let graph = star_graph(
        &server.path("root.star"),
        root_source,
        Some((&server.path("limits.star"), declaration)),
    );
    server.write("graph.json", &serde_json::to_string(&graph).unwrap());
    server.open("root.star", root_source, 1);
    let first = server.published("root.star");
    assert_eq!(first.version, Some(1));
    assert!(
        has_error(&first.diagnostics, "expected int, got str"),
        "{first:?}"
    );
    assert!(has_error(&first.diagnostics, "host signature"), "{first:?}");
    let record = first
        .diagnostics
        .iter()
        .find(|diagnostic| has_error(std::slice::from_ref(diagnostic), "expected int, got str"))
        .unwrap();
    assert_eq!(record.range.start.line, 2);
    assert_eq!(
        record.code,
        Some(lsp_types::Code::String("invalid-argument-type".into()))
    );
    let third_line = root_source.lines().nth(2).unwrap();
    assert_eq!(
        record.range.end.character,
        u32::try_from(third_line.strip_suffix(')').unwrap().encode_utf16().count()).unwrap()
    );
    assert!(record.range.end.character < u32::try_from(third_line.len()).unwrap());
    let related = record.related_information.as_ref().unwrap();
    assert_eq!(related[0].location.uri, server.uri("limits.star"));
    assert_eq!(related[0].location.range.start.line, 2);
    let overlays: serde_json::Value =
        serde_json::from_slice(&fs::read(server.path("captured.json")).unwrap()).unwrap();
    assert_eq!(overlays["version"], "sty-star-overlays-v1");
    assert_eq!(overlays["sources"].as_array().unwrap().len(), 1);
    assert_eq!(
        overlays["sources"][0]["path"],
        server
            .path("root.star")
            .canonicalize()
            .unwrap()
            .to_str()
            .unwrap()
    );
    assert_eq!(overlays["sources"][0]["source"], root_source);
    assert_eq!(
        fs::read_to_string(server.path("root.star")).unwrap(),
        "GOOD = 1\n"
    );

    let graph = star_graph(
        &server.path("root.star"),
        root_source,
        Some((&server.path("limits.star"), &loaded_source)),
    );
    server.write("graph.json", &serde_json::to_string(&graph).unwrap());
    server.open("limits.star", &loaded_source, 3);
    let loaded = server.published("limits.star");
    assert_eq!(loaded.version, Some(3));
    assert!(
        has_error(&loaded.diagnostics, "expected int, got str"),
        "{loaded:?}"
    );
    let root = server.published("root.star");
    assert!(
        has_error(&root.diagnostics, "expected int, got str"),
        "{root:?}"
    );
    let overlays: serde_json::Value =
        serde_json::from_slice(&fs::read(server.path("captured.json")).unwrap()).unwrap();
    assert_eq!(overlays["sources"].as_array().unwrap().len(), 2);
    assert_eq!(overlays["sources"][0]["source"], root_source);
    assert_eq!(overlays["sources"][1]["source"], loaded_source);
    assert_eq!(
        fs::read_to_string(server.path("limits.star")).unwrap(),
        declaration
    );

    let graph = star_graph(
        &server.path("root.star"),
        root_source,
        Some((&server.path("limits.star"), declaration)),
    );
    server.write("graph.json", &serde_json::to_string(&graph).unwrap());
    server.close("limits.star");
    let restored = server.published("limits.star");
    assert_eq!(restored.version, None);
    assert!(restored.diagnostics.is_empty(), "{restored:?}");
    let root = server.published("root.star");
    assert!(
        has_error(&root.diagnostics, "expected int, got str"),
        "{root:?}"
    );
    let overlays: serde_json::Value =
        serde_json::from_slice(&fs::read(server.path("captured.json")).unwrap()).unwrap();
    assert_eq!(overlays["sources"].as_array().unwrap().len(), 1);
    assert_eq!(overlays["sources"][0]["source"], root_source);
}

#[cfg(unix)]
#[test]
fn opaque_loaded_star_blocks_an_open_root_with_related_file_uri() {
    let server = TestServer::with_options(host_settings);
    let source = "load(\"//example:limits.star\", \"LimitConfig\")\nGOOD = 1\n";
    let invalid = "def broken(:\n";
    server.write("root.star", source);
    server.write("limits.star", invalid);
    server.write(
        "graph.json",
        &serde_json::to_string(&star_graph(
            &server.path("root.star"),
            source,
            Some((&server.path("limits.star"), invalid)),
        ))
        .unwrap(),
    );
    server.open("root.star", source, 4);
    let loaded = server.published("limits.star");
    assert!(has_error(&loaded.diagnostics, "parser"), "{loaded:?}");
    let root = server.published("root.star");
    assert_eq!(root.version, Some(4));
    assert!(
        has_error(&root.diagnostics, "loaded source is opaque"),
        "{root:?}"
    );
    assert_eq!(
        root.diagnostics[0].related_information.as_ref().unwrap()[0]
            .location
            .uri,
        server.uri("limits.star")
    );
    server.no_pending_publication();
}

#[cfg(unix)]
#[test]
fn loaded_star_alone_sees_the_concrete_host_failure() {
    let server = TestServer::with_options(host_settings);
    server.write("root.star", "GOOD = 1\n");
    server.write("limits.star", "GOOD = 1\n");
    fs::write(
        server.path("host-checker"),
        "#!/bin/sh\necho 'private loader failed' >&2\nexit 47\n",
    )
    .unwrap();
    server.open("limits.star", "GOOD = 1\n", 9);
    let loaded = server.published("limits.star");
    assert_eq!(loaded.version, Some(9));
    assert!(
        has_error(&loaded.diagnostics, "private loader failed"),
        "{loaded:?}"
    );
    let root = server.published("root.star");
    assert_eq!(root.version, None);
    assert!(
        has_error(&root.diagnostics, "private loader failed"),
        "{root:?}"
    );
    server.no_pending_publication();
}

#[cfg(unix)]
#[test]
fn mismatched_open_loaded_snapshot_fails_without_partial_type_claims() {
    let server = TestServer::with_options(host_settings);
    let source = "load(\"//example:limits.star\", \"LimitConfig\")\nLimitConfig(max_connections=\"wrong\")\n";
    let declaration = "LimitConfig = record(max_connections=int)\n";
    server.write("root.star", source);
    server.write("limits.star", declaration);
    server.write(
        "graph.json",
        &serde_json::to_string(&star_graph(
            &server.path("root.star"),
            source,
            Some((&server.path("limits.star"), declaration)),
        ))
        .unwrap(),
    );
    server.open("root.star", source, 1);
    assert!(has_error(
        &server.published("root.star").diagnostics,
        "expected int, got str"
    ));
    server.open(
        "limits.star",
        "LimitConfig = record(max_connections=str)\n",
        2,
    );
    let loaded = server.published("limits.star");
    assert_eq!(loaded.version, Some(2));
    assert!(
        has_error(&loaded.diagnostics, "snapshot differs"),
        "{loaded:?}"
    );
    let root = server.published("root.star");
    assert_eq!(root.diagnostics.len(), 1, "{root:?}");
    assert!(has_error(&root.diagnostics, "snapshot differs"), "{root:?}");
    assert!(!has_error(&root.diagnostics, "expected int, got str"));
    server.no_pending_publication();
}

#[cfg(unix)]
#[test]
fn stale_host_graph_completion_never_publishes_an_old_editor_version() {
    let server = TestServer::with_options(|root| {
        let mut settings = host_settings(root);
        settings["hostSources"][0]["inputs"]["started"] = serde_json::json!(root.join("started"));
        settings["hostSources"][0]["inputs"]["release"] = serde_json::json!(root.join("release"));
        settings
    });
    let latest =
        "LimitConfig = record(max_connections=int)\nLimitConfig(max_connections=\"wrong\")\n";
    server.write("root.star", "GOOD = 1\n");
    server.write(
        "graph.json",
        &serde_json::to_string(&star_graph(&server.path("root.star"), latest, None)).unwrap(),
    );
    server.open("root.star", "GOOD = 1\n", 1);
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    while !server.path("started").exists() && std::time::Instant::now() < deadline {
        thread::sleep(Duration::from_millis(20));
    }
    let started = server.path("started").exists();
    if !started {
        server.write("release", "");
    }
    assert!(started, "producer was not started");
    server.change("root.star", 2, &serde_json::json!([{"text":latest}]));
    server.no_pending_publication();
    server.write("release", "");
    let publication = server.published("root.star");
    assert_eq!(publication.version, Some(2), "{publication:?}");
    assert!(
        has_error(&publication.diagnostics, "expected int, got str"),
        "{publication:?}"
    );
    server.no_pending_publication();
}

#[cfg(unix)]
#[test]
fn two_open_aliases_report_setup_even_if_one_text_exceeds_the_host_limit() {
    let server = TestServer::with_options(host_settings);
    server.write("root.star", "GOOD = 1\n");
    server.write(
        "graph.json",
        &serde_json::to_string(&star_graph(&server.path("root.star"), "GOOD = 1\n", None)).unwrap(),
    );
    symlink(server.path("root.star"), server.path("alias.star")).unwrap();
    server.open("root.star", &"X".repeat(2 * 1024 * 1024 + 1), 1);
    let first = server.published("root.star");
    assert!(
        has_error(&first.diagnostics, "no frozen editor overlay"),
        "{first:?}"
    );
    fs::remove_file(server.path("captured.json")).unwrap();

    server.open("alias.star", "GOOD = 2\n", 4);
    let alias = server.published("alias.star");
    assert_eq!(alias.version, Some(4));
    assert!(
        has_error(&alias.diagnostics, "alias the same physical file"),
        "{alias:?}"
    );
    let root = server.published("root.star");
    assert!(
        has_error(&root.diagnostics, "alias the same physical file"),
        "{root:?}"
    );
    assert!(
        !server.path("captured.json").exists(),
        "duplicate aliases started a host process"
    );
    server.no_pending_publication();
}

#[cfg(unix)]
#[test]
fn an_unrelated_oversized_open_star_does_not_break_the_root_check() {
    let server = TestServer::with_options(host_settings);
    let source =
        "LimitConfig = record(max_connections=int)\nLimitConfig(max_connections=\"wrong\")\n";
    server.write("root.star", "GOOD = 1\n");
    server.write("unrelated.star", "GOOD = 1\n");
    server.write(
        "graph.json",
        &serde_json::to_string(&star_graph(&server.path("root.star"), source, None)).unwrap(),
    );
    server.open("unrelated.star", &"X".repeat(2 * 1024 * 1024 + 1), 2);
    let unrelated = server.published("unrelated.star");
    assert!(
        has_error(&unrelated.diagnostics, "configured host roots did not load"),
        "{unrelated:?}"
    );
    server.open("root.star", source, 3);
    let root = server.published("root.star");
    assert!(
        has_error(&root.diagnostics, "expected int, got str"),
        "{root:?}"
    );
    let unrelated = server.published("unrelated.star");
    assert!(
        has_error(&unrelated.diagnostics, "configured host roots did not load"),
        "{unrelated:?}"
    );
    let overlays: serde_json::Value =
        serde_json::from_slice(&fs::read(server.path("captured.json")).unwrap()).unwrap();
    assert_eq!(overlays["sources"].as_array().unwrap().len(), 1);
    assert_eq!(overlays["sources"][0]["source"], source);
    server.no_pending_publication();
}

#[cfg(unix)]
fn host_settings(root: &Path) -> serde_json::Value {
    let checker = root.join("host-checker");
    fs::write(
        &checker,
        concat!(
            "#!/bin/sh\n",
            "[ \"$1\" = '--sty-graph-v3' ] || exit 41\n",
            "GRAPH='' CAPTURE='' DELAY='' OVERLAY=0\n",
            "while [ \"$#\" -gt 0 ]; do\n",
            "  case \"$1\" in\n",
            "    --sty-graph-v3) shift;;\n",
            "    --source) SOURCE=\"$2\"; shift 2;;\n",
            "    --sty-overlays-stdin) OVERLAY=1; shift;;\n",
            "    --input) case \"$2\" in\n",
            "      graph=*) GRAPH=\"${2#graph=}\";;\n",
            "      capture=*) CAPTURE=\"${2#capture=}\";;\n",
            "      delay=*) DELAY=\"${2#delay=}\";;\n",
            "      started=*) STARTED=\"${2#started=}\";;\n",
            "      release=*) RELEASE=\"${2#release=}\";;\n",
            "      *) exit 42;;\n",
            "    esac; shift 2;;\n",
            "    *) exit 43;;\n",
            "  esac\n",
            "done\n",
            "[ \"$OVERLAY\" -eq 1 ] || { echo 'no overlay interface' >&2; exit 44; }\n",
            "[ -z \"$STARTED\" ] || printf 'started' > \"$STARTED\"\n",
            "[ -z \"$RELEASE\" ] || while [ ! -e \"$RELEASE\" ]; do sleep 0.01; done\n",
            "[ -z \"$DELAY\" ] || sleep \"$(cat \"$DELAY\")\"\n",
            "cat > \"$CAPTURE\" || exit 45\n",
            "cat \"$GRAPH\" || exit 46\n",
        ),
    )
    .unwrap();
    let mut permissions = fs::metadata(&checker).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&checker, permissions).unwrap();
    serde_json::json!({"hostSources": [{
        "root": root.join("root.star"), "checker": checker,
        "inputs": {"graph":root.join("graph.json"), "capture":root.join("captured.json")}
    }]})
}

#[cfg(unix)]
fn star_graph(root: &Path, text: &str, loaded: Option<(&Path, &str)>) -> serde_json::Value {
    let (loads, modules) = if let Some((path, source)) = loaded {
        let literal = "\"//example:limits.star\"";
        let start = text.find(literal).unwrap();
        (
            vec![serde_json::json!({
                "module_id":"//example:limits.star", "start":start, "end":start+literal.len(),
                "symbols":[{"local":"LimitConfig", "source":"LimitConfig"}]
            })],
            vec![serde_json::json!({
                "id":"//example:limits.star", "path":path, "source":source, "loads":[]
            })],
        )
    } else {
        (vec![], vec![])
    };
    serde_json::json!({
        "version":"sty-star-graph-v3", "profile":"example-star-host-v3",
        "root":{"path":root, "source":text, "loads":loads}, "modules":modules,
        "special_forms":[
            {"name":"record", "kind":"builtin_record", "validator":"none",
                "field_types":"named_keyword_type_expressions"},
            {"name":"wrapper_record", "kind":"record_with_validator",
                "validator":"first_positional_callable",
                "field_types":"named_keyword_type_expressions"}
        ],
        "intrinsics":[
            {"name":"field", "kind":"field_first_type_optional_default"},
            {"name":"struct", "kind":"struct_named_members"}
        ],
        "host_functions":[{"name":"example_host_native","params":[
            {"name":"value", "mode":"pos_or_named", "required":true, "type":"str"}
        ],"returns":"str", "availability":"any_module"}]
    })
}

#[test]
fn unsaved_bazel_source_reports_utf16_and_related_uri_then_restores_disk() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("shared/BUILD", "");
    server.write(
        "shared/defs.bzl",
        "def identity(value):\n    return value\n",
    );
    server.write("pkg/BUILD", "");
    let disk = "load(\"//shared:defs.bzl\", \"identity\")\ndef valid():\n    return identity(1)\n";
    server.write("pkg/entry.bzl", disk);
    let editor = "load(\"//shared:defs.bzl\", \"identity\")\ndef invalid():\n    return identity(\"😀\", 2)\n";
    server.open("pkg/entry.bzl", editor, 1);
    let publication = server.published("pkg/entry.bzl");
    assert_eq!(publication.version, Some(1));
    assert_eq!(publication.diagnostics.len(), 1, "{publication:?}");
    let error = &publication.diagnostics[0];
    assert_eq!(
        error.code,
        Some(lsp_types::Code::String("invalid-argument-count".into()))
    );
    assert!(
        has_error(&publication.diagnostics, "expects 1 positional argument"),
        "{publication:?}"
    );
    assert_eq!(error.range.start.line, 2);
    assert_eq!(error.range.start.character, 11);
    assert_eq!(error.range.end.character, 28);
    assert_eq!(
        error.related_information.as_ref().unwrap()[0].location.uri,
        server.uri("shared/defs.bzl")
    );
    server.no_pending_publication();

    server.change(
        "pkg/entry.bzl",
        2,
        &serde_json::json!([{"range":{"start":{"line":2,"character":24},"end":{"line":2,"character":27}},"text":""}]),
    );
    let repaired = server.published("pkg/entry.bzl");
    assert_eq!(repaired.version, Some(2));
    assert!(repaired.diagnostics.is_empty(), "{repaired:?}");
    server.no_pending_publication();
    server.change("pkg/entry.bzl", 1, &serde_json::json!([{"text":editor}]));
    server.no_pending_publication();
    server.close("pkg/entry.bzl");
    let closed = server.published("pkg/entry.bzl");
    assert_eq!(closed.version, None);
    assert!(closed.diagnostics.is_empty(), "{closed:?}");
    assert_eq!(
        fs::read_to_string(server.path("pkg/entry.bzl")).unwrap(),
        disk
    );
}

#[test]
fn unsaved_loaded_file_and_stub_recheck_importer_and_close_restores_disk() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("lib/BUILD", "");
    let disk = "def identity(value):\n    return value\n";
    server.write("lib/defs.bzl", disk);
    server.write("pkg/BUILD", "");
    let root = "load(\"//lib:defs.bzl\", \"identity\")\ndef consumer():\n    return identity(1)\n";
    server.write("pkg/entry.bzl", root);
    server.open("pkg/entry.bzl", root, 1);
    let importer = server.published("pkg/entry.bzl");
    assert!(importer.diagnostics.is_empty(), "{importer:?}");

    server.open(
        "lib/defs.bzl",
        "def identity(value, extra):\n    return value\n",
        1,
    );
    let changed = server.published("pkg/entry.bzl");
    assert!(
        has_error(&changed.diagnostics, "expects 2 positional arguments"),
        "{changed:?}"
    );
    server.close("lib/defs.bzl");
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
    assert_eq!(
        fs::read_to_string(server.path("lib/defs.bzl")).unwrap(),
        disk
    );

    server.write("lib/defs.bzl.pyi", "def identity(value: int) -> int: ...\n");
    server.notify(
        "workspace/didChangeWatchedFiles",
        serde_json::json!({"changes":[{"uri":server.uri("lib/defs.bzl.pyi"),"type":1}]}),
    );
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
    server.open(
        "lib/defs.bzl.pyi",
        "def identity(value: str) -> str: ...\n",
        1,
    );
    let changed = server.published("pkg/entry.bzl");
    assert!(
        has_error(&changed.diagnostics, "can receive int"),
        "{changed:?}"
    );
    server.close("lib/defs.bzl.pyi");
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
}

#[test]
fn unsaved_build_and_repository_marker_admit_open_source() {
    let server = TestServer::new();
    server.write("pkg/entry.bzl", "GOOD = 1\n");
    server.open("pkg/entry.bzl", "GOOD = 1\n", 1);
    assert!(has_error(
        &server.published("pkg/entry.bzl").diagnostics,
        "no Bazel repository marker"
    ));
    server.open("MODULE.bazel", "", 1);
    let selected = server.published("pkg/entry.bzl");
    assert!(
        has_error(&selected.diagnostics, "outside a Bazel package"),
        "{selected:?}"
    );
    server.open("pkg/BUILD.bazel", "", 1);
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
    server.close("pkg/BUILD.bazel");
    assert!(has_error(
        &server.published("pkg/entry.bzl").diagnostics,
        "outside a Bazel package"
    ));
    server.close("MODULE.bazel");
    assert!(has_error(
        &server.published("pkg/entry.bzl").diagnostics,
        "no Bazel repository marker"
    ));
}

#[test]
fn loaded_file_diagnostics_are_cleared_when_dependency_disappears() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    server.write(
        "pkg/defs.bzl",
        "def foo(value):\n    return value\ndef error():\n    return foo(1, 2)\n",
    );
    let root = "load(\":defs.bzl\", \"foo\")\ndef use():\n    return foo(1)\n";
    server.write("pkg/entry.bzl", root);
    server.open("pkg/entry.bzl", root, 1);
    assert!(has_error(
        &server.published("pkg/defs.bzl").diagnostics,
        "expects 1 positional argument"
    ));
    let importer = server.published("pkg/entry.bzl");
    assert!(importer.diagnostics.is_empty(), "{importer:?}");
    server.change(
        "pkg/entry.bzl",
        2,
        &serde_json::json!([{"text":"def use():\n    return 1\n"}]),
    );
    assert!(server.published("pkg/defs.bzl").diagnostics.is_empty());
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
    server.no_pending_publication();
}

#[test]
fn new_unsaved_bazel_file_is_selectable_in_an_existing_package() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    let new_path = server.path("pkg/new.bzl");
    assert!(!new_path.exists());
    server.open(
        "pkg/new.bzl",
        "def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n",
        1,
    );
    let publication = server.published("pkg/new.bzl");
    assert!(
        has_error(&publication.diagnostics, "expects 1 positional argument"),
        "{publication:?}"
    );
    assert!(!new_path.exists());
    server.close("pkg/new.bzl");
    assert!(server.published("pkg/new.bzl").diagnostics.is_empty());
}

#[test]
fn utf16_incremental_change_replaces_the_intended_bytes() {
    let text = "A😀BC\n".to_owned();
    let changed = apply_changes(
        text,
        serde_json::from_value(serde_json::json!([{"range":{"start":{"line":0,"character":3},"end":{"line":0,"character":4}},"text":"X"}])).unwrap(),
        Encoding::Utf16,
    )
    .unwrap();
    assert_eq!(changed, "A😀XC\n");
}

#[test]
fn bad_editor_notifications_log_an_error_and_preserve_following_edits() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    server.write("pkg/entry.bzl", "GOOD = 1\n");
    server.open("pkg/entry.bzl", "GOOD = 1\n", 1);
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());

    server.change(
        "pkg/unknown.bzl",
        2,
        &serde_json::json!([{"text":"GOOD = 2\n"}]),
    );
    server.logged_error("change for unopened document");
    server.notify("textDocument/didOpen", serde_json::json!({
        "textDocument":{"uri":"https://example.com/source.bzl","languageId":"starlark","version":1,"text":"GOOD = 2\n"}
    }));
    server.logged_error("Sty checks only file URIs");
    server.change("pkg/entry.bzl", 2, &serde_json::json!([{
        "range":{"start":{"line":1,"character":0},"end":{"line":0,"character":0}},"text":"BROKEN = 1\n"
    }]));
    server.logged_error("inverted source range");
    server.no_pending_publication();

    server.change(
        "pkg/entry.bzl",
        2,
        &serde_json::json!([{
            "text":"def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n"
        }]),
    );
    let publication = server.published("pkg/entry.bzl");
    assert_eq!(publication.version, Some(2));
    assert!(has_error(
        &publication.diagnostics,
        "expects 1 positional argument"
    ));
    server.no_pending_publication();
}

#[test]
fn opened_percent_encoded_uri_owns_the_versioned_source_diagnostic() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    server.write("pkg/entry.bzl", "GOOD = 1\n");
    let original = server.uri("pkg/entry.bzl");
    let alternate = Uri::parse(&original.as_str().replace("entry.bzl", "%65ntry.bzl")).unwrap();
    assert_ne!(alternate, original);
    server.notify(
        "textDocument/didOpen",
        serde_json::json!({
            "textDocument":{"uri":alternate,"languageId":"starlark","version":7,
                "text":"def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n"}
        }),
    );
    let publication = server.published_uri(&alternate);
    assert_eq!(publication.uri, alternate);
    assert_eq!(publication.version, Some(7));
    assert!(has_error(
        &publication.diagnostics,
        "expects 1 positional argument"
    ));
    server.no_pending_publication();
}

#[test]
fn simultaneous_sources_in_nested_repositories_keep_independent_graphs() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    server.write(
        "pkg/outer.bzl",
        "def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n",
    );
    server.write("nested/MODULE.bazel", "");
    server.write("nested/pkg/BUILD", "");
    server.write("nested/pkg/inner.bzl", "GOOD = 1\n");
    server.open(
        "pkg/outer.bzl",
        "def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n",
        1,
    );
    assert!(has_error(
        &server.published("pkg/outer.bzl").diagnostics,
        "expects 1 positional argument"
    ));
    server.open("nested/pkg/inner.bzl", "GOOD = 1\n", 1);
    assert!(
        server
            .published("nested/pkg/inner.bzl")
            .diagnostics
            .is_empty()
    );
    assert!(has_error(
        &server.published("pkg/outer.bzl").diagnostics,
        "expects 1 positional argument"
    ));
    server.no_pending_publication();
}

#[test]
fn shutdown_prevents_queued_edits_from_mutating_the_source() {
    let server = TestServer::new();
    server.write("MODULE.bazel", "");
    server.write("pkg/BUILD", "");
    server.write("pkg/entry.bzl", "GOOD = 1\n");
    server.open("pkg/entry.bzl", "GOOD = 1\n", 1);
    assert!(server.published("pkg/entry.bzl").diagnostics.is_empty());
    server
        .connection
        .sender
        .send(Message::Request(Request {
            id: RequestId::from(2),
            method: "shutdown".into(),
            params: serde_json::Value::Null,
        }))
        .unwrap();
    server.change(
        "pkg/entry.bzl",
        2,
        &serde_json::json!([{
            "text":"def foo(value):\n    return value\ndef bad():\n    return foo(1, 2)\n"
        }]),
    );
    let response = server
        .connection
        .receiver
        .recv_timeout(Duration::from_secs(5))
        .unwrap();
    let Message::Response(response) = response else {
        panic!("expected shutdown response, got {response:?}");
    };
    assert_eq!(response.id, RequestId::from(2));
    assert!(response.response_result.is_ok());
    server.no_pending_publication();
}
