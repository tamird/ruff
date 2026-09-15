use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _};

use crate::testing::test_db;

use super::{BazelLoadError, BazelRepository, resolve_bazel_load};

#[test]
fn resolves_named_packages_and_selects_stubs() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("BUILD.bazel", ""),
        ("root.bzl", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/defs.bzl.pyi", ""),
        ("pkg/sub/BUILD.bazel", ""),
        ("pkg/sub/defs.bzl", ""),
        ("shared/BUILD.bazel", ""),
        ("shared/defs.bzl", ""),
        ("shared/defs.bzl.pyi", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    let local_source = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let local_stub = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;

    for label in [":defs.bzl", "//pkg:defs.bzl"] {
        let loaded = resolve_bazel_load(&db, repository, importer, label)?;
        assert_eq!(loaded.source, local_source);
        assert_eq!(loaded.stub, Some(local_stub));
        assert_eq!(loaded.type_file(), local_stub);
    }

    let loaded = resolve_bazel_load(&db, repository, importer, "//shared:defs.bzl")?;
    let shared_source = system_path_to_file(&db, root.join("shared/defs.bzl"))?;
    let shared_stub = system_path_to_file(&db, root.join("shared/defs.bzl.pyi"))?;
    assert_eq!(loaded.source, shared_source);
    assert_eq!(loaded.stub, Some(shared_stub));

    for (label, path) in [
        ("//:root.bzl", "root.bzl"),
        ("//pkg/sub:defs.bzl", "pkg/sub/defs.bzl"),
    ] {
        let loaded = resolve_bazel_load(&db, repository, importer, label)?;
        assert_eq!(loaded.source.path(&db), &root.join(path));
        assert_eq!(loaded.stub, None);
    }
    Ok(())
}

#[test]
fn selected_root_and_importer_must_belong_to_the_same_repository() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/sub/MODULE.bazel", ""),
        ("pkg/sub/BUILD.bazel", ""),
        ("pkg/sub/importer.bzl", ""),
        ("pkg/sub/defs.bzl", ""),
    ])?;
    let outer = BazelRepository::new(&db, root.clone());
    let nested_root = root.join("pkg/sub");
    let nested = BazelRepository::new(&db, nested_root.clone());
    let importer = system_path_to_file(&db, nested_root.join("importer.bzl"))?;

    assert_eq!(
        resolve_bazel_load(&db, outer, importer, "//:defs.bzl"),
        Err(BazelLoadError::InvalidRepository)
    );
    let loaded = resolve_bazel_load(&db, nested, importer, "//:defs.bzl")?;
    assert_eq!(loaded.source.path(&db), &nested_root.join("defs.bzl"));

    db.write_file(root.join("MODULE.bazel"), "")?;
    let outer = BazelRepository::new(&db, root.clone());
    let nested = BazelRepository::new(&db, nested_root.clone());
    assert_eq!(
        resolve_bazel_load(&db, outer, importer, "//:defs.bzl"),
        Err(BazelLoadError::ImporterOutsideRepository)
    );
    let loaded = resolve_bazel_load(&db, nested, importer, "//:defs.bzl")?;
    assert_eq!(loaded.source.path(&db), &nested_root.join("defs.bzl"));

    let outer_importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    assert_eq!(
        resolve_bazel_load(&db, nested, outer_importer, "//:defs.bzl"),
        Err(BazelLoadError::ImporterOutsideRepository)
    );
    Ok(())
}

#[test]
fn refuses_non_bzl_importers_and_missing_importer_packages() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/main.star", ""),
        ("unowned/main.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let star = system_path_to_file(&db, root.join("pkg/main.star"))?;
    assert_eq!(
        resolve_bazel_load(&db, repository, star, "//pkg:defs.bzl"),
        Err(BazelLoadError::InvalidImporter)
    );

    let unowned = system_path_to_file(&db, root.join("unowned/main.bzl"))?;
    assert_eq!(
        resolve_bazel_load(&db, repository, unowned, "//pkg:defs.bzl"),
        Err(BazelLoadError::ImporterOutsidePackage)
    );
    Ok(())
}

#[test]
fn rejects_missing_packages_and_nested_boundaries() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("REPO.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("pkg/sub/BUILD.bazel", ""),
        ("pkg/sub/defs.bzl", ""),
        ("pkg/nested/WORKSPACE", ""),
        ("pkg/nested/BUILD", ""),
        ("pkg/nested/defs.bzl", ""),
        ("other/BUILD.bazel", ""),
        ("other/sub/BUILD", ""),
        ("other/sub/defs.bzl", ""),
        ("other/no-build/defs.bzl", ""),
        ("pkg/stub-only.bzl.pyi", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;

    for label in [
        ":sub/defs.bzl",
        "//pkg:sub/defs.bzl",
        "//other:sub/defs.bzl",
    ] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label),
            Err(BazelLoadError::PackageBoundary)
        );
    }
    for label in ["//pkg/nested:defs.bzl", "//pkg:nested/defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label),
            Err(BazelLoadError::RepositoryBoundary)
        );
    }
    for label in ["//missing:defs.bzl", "//other/no-build:defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label),
            Err(BazelLoadError::UnknownTargetPackage)
        );
    }
    for label in [
        ":../defs.bzl",
        "//pkg:/defs.bzl",
        ":defs.star",
        "//pkg:sub//defs.bzl",
    ] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label),
            Err(BazelLoadError::InvalidLabel)
        );
    }
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "@external//pkg:defs.bzl"),
        Err(BazelLoadError::UnsupportedRepository)
    );
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, ":stub-only.bzl"),
        Err(BazelLoadError::NotFound)
    );
    Ok(())
}

#[test]
fn observes_marker_stub_and_source_changes() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("other/defs.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    let source_path = root.join("other/defs.bzl");
    let stub_path = root.join("other/defs.bzl.pyi");
    let nested_marker = root.join("other/MODULE.bazel");

    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl"),
        Err(BazelLoadError::UnknownTargetPackage)
    );
    db.write_file(root.join("other/BUILD.bazel"), "")?;
    let repository = BazelRepository::new(&db, root.clone());
    let original = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    assert_eq!(original.source.path(&db), &source_path);
    assert_eq!(original.stub, None);

    db.write_file(&stub_path, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    let stubbed = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    let stub = system_path_to_file(&db, &stub_path)?;
    assert_eq!(stubbed.stub, Some(stub));
    assert_eq!(stubbed.type_file(), stub);

    db.write_file(&nested_marker, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl"),
        Err(BazelLoadError::RepositoryBoundary)
    );
    db.memory_file_system().remove_file(&nested_marker)?;
    File::sync_path(&mut db, &nested_marker);
    let repository = BazelRepository::new(&db, root.clone());
    let loaded = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    assert_eq!(loaded.source, original.source);

    db.memory_file_system().remove_file(&source_path)?;
    File::sync_path(&mut db, &source_path);
    let repository = BazelRepository::new(&db, root);
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl"),
        Err(BazelLoadError::NotFound)
    );
    Ok(())
}
