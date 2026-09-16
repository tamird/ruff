use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicI32, Ordering};
use std::thread::{self, JoinHandle};
use std::time::Duration;

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
        let root = tempfile::tempdir().unwrap();
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
                params: serde_json::json!({"capabilities": {}}),
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
