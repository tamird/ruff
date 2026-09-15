use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _, SystemPath};

use crate::stub::{BazelStubAdmission, admit_bazel_stub};
use crate::testing::test_db;

use super::{BazelLoadError, BazelRepository, resolve_bazel_load, resolve_bazel_target};

#[test]
fn resolves_named_packages_and_runtime_sources() -> anyhow::Result<()> {
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
        assert_eq!(loaded.selected_file(&db), local_source);
        let BazelStubAdmission::Admitted(stub) = admit_bazel_stub(&db, loaded) else {
            anyhow::bail!("expected a checked sibling stub for {label}");
        };
        assert_eq!(stub.file(), local_stub);
    }

    let loaded = resolve_bazel_load(&db, repository, importer, "//shared:defs.bzl")?;
    let shared_source = system_path_to_file(&db, root.join("shared/defs.bzl"))?;
    let shared_stub = system_path_to_file(&db, root.join("shared/defs.bzl.pyi"))?;
    assert_eq!(loaded.selected_file(&db), shared_source);
    let BazelStubAdmission::Admitted(stub) = admit_bazel_stub(&db, loaded) else {
        anyhow::bail!("expected a checked sibling stub for the shared source");
    };
    assert_eq!(stub.file(), shared_stub);

    for (label, path) in [
        ("//:root.bzl", "root.bzl"),
        ("//pkg/sub:defs.bzl", "pkg/sub/defs.bzl"),
    ] {
        let loaded = resolve_bazel_load(&db, repository, importer, label)?;
        assert_eq!(loaded.selected_file(&db).path(&db), &root.join(path));
        assert!(matches!(
            admit_bazel_stub(&db, loaded),
            BazelStubAdmission::Absent
        ));
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
        resolve_bazel_load(&db, outer, importer, "//:defs.bzl").err(),
        Some(BazelLoadError::InvalidRepository)
    );
    let loaded = resolve_bazel_load(&db, nested, importer, "//:defs.bzl")?;
    assert_eq!(
        loaded.selected_file(&db).path(&db),
        &nested_root.join("defs.bzl")
    );

    db.write_file(root.join("MODULE.bazel"), "")?;
    let outer = BazelRepository::new(&db, root.clone());
    let nested = BazelRepository::new(&db, nested_root.clone());
    assert_eq!(
        resolve_bazel_load(&db, outer, importer, "//:defs.bzl").err(),
        Some(BazelLoadError::ImporterOutsideRepository)
    );
    let loaded = resolve_bazel_load(&db, nested, importer, "//:defs.bzl")?;
    assert_eq!(
        loaded.selected_file(&db).path(&db),
        &nested_root.join("defs.bzl")
    );

    let outer_importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    assert_eq!(
        resolve_bazel_load(&db, nested, outer_importer, "//:defs.bzl").err(),
        Some(BazelLoadError::ImporterOutsideRepository)
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
        resolve_bazel_load(&db, repository, star, "//pkg:defs.bzl").err(),
        Some(BazelLoadError::InvalidImporter)
    );

    let unowned = system_path_to_file(&db, root.join("unowned/main.bzl"))?;
    assert_eq!(
        resolve_bazel_load(&db, repository, unowned, "//pkg:defs.bzl").err(),
        Some(BazelLoadError::ImporterOutsidePackage)
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
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::PackageBoundary)
        );
    }
    for label in ["//pkg/nested:defs.bzl", "//pkg:nested/defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::RepositoryBoundary)
        );
    }
    for label in ["//missing:defs.bzl", "//other/no-build:defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::UnknownTargetPackage)
        );
    }
    for label in [
        ":../defs.bzl",
        "//pkg:/defs.bzl",
        ":defs.star",
        "//pkg:sub//defs.bzl",
    ] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::InvalidLabel)
        );
    }
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "@external//pkg:defs.bzl").err(),
        Some(BazelLoadError::UnsupportedRepository)
    );
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, ":stub-only.bzl").err(),
        Some(BazelLoadError::NotFound)
    );
    Ok(())
}

#[test]
fn explicit_main_repository_labels_use_the_selected_root() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("BUILD.bazel", ""),
        ("root.bzl", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("shared/BUILD", ""),
        ("shared/defs.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;

    for (label, path) in [
        ("//shared:defs.bzl", "shared/defs.bzl"),
        ("@@//shared:defs.bzl", "shared/defs.bzl"),
        ("//:root.bzl", "root.bzl"),
        ("@@//:root.bzl", "root.bzl"),
    ] {
        let loaded = resolve_bazel_load(&db, repository, importer, label)?;
        assert_eq!(
            loaded.selected_file(&db).path(&db),
            &root.join(path),
            "{label}"
        );
    }
    for label in ["@external//shared:defs.bzl", "@@external//shared:defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::UnsupportedRepository)
        );
    }
    Ok(())
}

#[test]
fn target_names_reject_spaces_controls_and_unicode_even_for_existing_files() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("REPO.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("pkg/foo bar.bzl", ""),
        ("pkg/déf.bzl", ""),
        ("pkg/new\nline.bzl", ""),
        ("pkg/good+defs.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;

    for label in [
        ":foo bar.bzl",
        "//pkg:foo bar.bzl",
        ":déf.bzl",
        ":new\nline.bzl",
        "@@//pkg:foo bar.bzl",
    ] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::InvalidLabel),
            "{label:?}"
        );
    }
    let loaded = resolve_bazel_load(&db, repository, importer, ":good+defs.bzl")?;
    assert_eq!(
        loaded.selected_file(&db).path(&db),
        &root.join("pkg/good+defs.bzl")
    );
    Ok(())
}

#[test]
fn package_names_preserve_spaces_and_reject_invalid_components() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("shared space/BUILD", ""),
        ("shared space/defs.bzl", ""),
        ("bad~/BUILD", ""),
        ("bad~/defs.bzl", ""),
        ("dép/BUILD", ""),
        ("dép/defs.bzl", ""),
        ("dots/.../BUILD", ""),
        ("dots/.../defs.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let importer = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    for label in ["//shared space:defs.bzl", "@@//shared space:defs.bzl"] {
        let loaded = resolve_bazel_load(&db, repository, importer, label)?;
        assert_eq!(
            loaded.selected_file(&db).path(&db),
            &root.join("shared space/defs.bzl")
        );
    }
    for label in ["//bad~:defs.bzl", "//dép:defs.bzl", "//dots/...:defs.bzl"] {
        assert_eq!(
            resolve_bazel_load(&db, repository, importer, label).err(),
            Some(BazelLoadError::InvalidLabel),
            "{label}"
        );
    }
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
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl").err(),
        Some(BazelLoadError::UnknownTargetPackage)
    );
    db.write_file(root.join("other/BUILD.bazel"), "")?;
    let repository = BazelRepository::new(&db, root.clone());
    let original = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    let original_file = original.selected_file(&db);
    assert_eq!(original_file.path(&db), &source_path);
    assert!(matches!(
        admit_bazel_stub(&db, original),
        BazelStubAdmission::Absent
    ));

    db.write_file(&stub_path, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    let unchanged_source = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    assert_eq!(unchanged_source.selected_file(&db), original_file);
    let BazelStubAdmission::Admitted(stub) = admit_bazel_stub(&db, unchanged_source) else {
        anyhow::bail!("expected the newly created sibling stub");
    };
    assert_eq!(stub.file(), system_path_to_file(&db, &stub_path)?);

    db.write_file(&nested_marker, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl").err(),
        Some(BazelLoadError::RepositoryBoundary)
    );
    db.memory_file_system().remove_file(&nested_marker)?;
    File::sync_path(&mut db, &nested_marker);
    let repository = BazelRepository::new(&db, root.clone());
    let loaded = resolve_bazel_load(&db, repository, importer, "//other:defs.bzl")?;
    assert_eq!(loaded.selected_file(&db), original_file);

    db.memory_file_system().remove_file(&source_path)?;
    File::sync_path(&mut db, &source_path);
    let repository = BazelRepository::new(&db, root);
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, "//other:defs.bzl").err(),
        Some(BazelLoadError::NotFound)
    );
    Ok(())
}

#[test]
fn direct_absolute_targets_need_no_importer_or_cwd_package() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD.bazel", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/defs.bzl.pyi", ""),
        ("pkg/stub-only.bzl.pyi", ""),
        ("notes/README", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let cwd = root.join("notes");
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;

    for label in ["//pkg:defs.bzl", "@@//pkg:defs.bzl"] {
        let selected = resolve_bazel_target(&db, repository, Some(&cwd), label)?;
        assert_eq!(selected.selected_file(&db), source_file);
        let BazelStubAdmission::Admitted(stub) = admit_bazel_stub(&db, selected) else {
            anyhow::bail!("expected checked declarations for {label}");
        };
        assert_eq!(stub.file(), stub_file);
    }
    assert_eq!(
        resolve_bazel_target(&db, repository, None, "//pkg:stub-only.bzl").err(),
        Some(BazelLoadError::NotFound)
    );
    assert_eq!(
        resolve_bazel_target(&db, repository, None, "@external//pkg:defs.bzl").err(),
        Some(BazelLoadError::UnsupportedRepository)
    );
    assert_eq!(
        resolve_bazel_target(&db, repository, None, "//pkg:defs.star").err(),
        Some(BazelLoadError::InvalidLabel)
    );
    Ok(())
}

#[test]
fn direct_relative_targets_require_build_in_the_exact_cwd() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("WORKSPACE", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/sub/importer.bzl", ""),
        ("pkg/sub/README", ""),
        ("pkg/nested/BUILD.bazel", ""),
        ("pkg/nested/defs.bzl", ""),
    ])?;
    let repository = BazelRepository::new(&db, root.clone());
    let package = root.join("pkg");
    let subdirectory = root.join("pkg/sub");
    let nested = root.join("pkg/nested");
    let importer = system_path_to_file(&db, root.join("pkg/sub/importer.bzl"))?;
    let runtime = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;

    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&package), ":defs.bzl")?.selected_file(&db),
        runtime
    );
    assert_eq!(
        resolve_bazel_load(&db, repository, importer, ":defs.bzl")?.selected_file(&db),
        runtime
    );
    for directory in [&subdirectory, &root] {
        assert_eq!(
            resolve_bazel_target(&db, repository, Some(directory), ":defs.bzl").err(),
            Some(BazelLoadError::RelativeTargetOutsidePackage)
        );
    }
    assert_eq!(
        resolve_bazel_target(&db, repository, None, ":defs.bzl").err(),
        Some(BazelLoadError::MissingRelativeDirectory)
    );
    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&package), ":nested/defs.bzl").err(),
        Some(BazelLoadError::PackageBoundary)
    );
    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&nested), ":defs.bzl")?.selected_file(&db),
        system_path_to_file(&db, nested.join("defs.bzl"))?
    );
    Ok(())
}

#[test]
fn direct_targets_enforce_nested_and_selected_repository_roots() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", ""),
        ("pkg/inner/MODULE.bazel", ""),
        ("pkg/inner/BUILD", ""),
        ("pkg/inner/defs.bzl", ""),
    ])?;
    let outer = BazelRepository::new(&db, root.clone());
    let inner_root = root.join("pkg/inner");
    let inner = BazelRepository::new(&db, inner_root.clone());

    for label in ["//pkg/inner:defs.bzl", "//pkg:inner/defs.bzl"] {
        assert_eq!(
            resolve_bazel_target(&db, outer, None, label).err(),
            Some(BazelLoadError::RepositoryBoundary)
        );
    }
    assert_eq!(
        resolve_bazel_target(&db, outer, Some(&inner_root), ":defs.bzl").err(),
        Some(BazelLoadError::RelativeTargetOutsideRepository)
    );
    assert_eq!(
        resolve_bazel_target(&db, inner, Some(&root), ":defs.bzl").err(),
        Some(BazelLoadError::RelativeTargetOutsideRepository)
    );
    for label in ["//:defs.bzl", "@@//:defs.bzl"] {
        assert_eq!(
            resolve_bazel_target(&db, inner, None, label)?.selected_file(&db),
            system_path_to_file(&db, inner_root.join("defs.bzl"))?
        );
    }
    assert_eq!(
        resolve_bazel_target(&db, inner, Some(&inner_root), ":defs.bzl")?.selected_file(&db),
        system_path_to_file(&db, inner_root.join("defs.bzl"))?
    );
    Ok(())
}

#[test]
fn parent_traversal_cannot_alias_the_repository_or_relative_package() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", ""),
        ("pkg/defs.bzl", ""),
    ])?;
    let outside = root.join("pkg/../../foreign");
    db.memory_file_system().create_directory_all(&outside)?;
    db.write_file(outside.join("BUILD"), "")?;
    db.write_file(outside.join("defs.bzl"), "")?;
    assert!(system_path_to_file(&db, outside.join("defs.bzl")).is_ok());

    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&outside), ":defs.bzl").err(),
        Some(BazelLoadError::RelativeTargetParentTraversal)
    );
    let outside_directory = SystemPath::absolute(&outside, &root);
    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&outside_directory), ":defs.bzl").err(),
        Some(BazelLoadError::RelativeTargetOutsideRepository)
    );
    assert_eq!(
        resolve_bazel_target(&db, repository, Some(&root.join("pkg/../pkg")), ":defs.bzl").err(),
        Some(BazelLoadError::RelativeTargetParentTraversal)
    );
    let aliased_root = BazelRepository::new(&db, root.join("pkg/.."));
    assert_eq!(
        resolve_bazel_target(&db, aliased_root, None, "//pkg:defs.bzl").err(),
        Some(BazelLoadError::InvalidRepository)
    );
    let aliased_importer = system_path_to_file(&db, root.join("pkg/../pkg/importer.bzl"))?;
    assert_eq!(aliased_importer.path(&db), &root.join("pkg/importer.bzl"));
    assert_eq!(
        resolve_bazel_load(&db, repository, aliased_importer, "//pkg:defs.bzl")?.selected_file(&db),
        system_path_to_file(&db, root.join("pkg/defs.bzl"))?
    );
    Ok(())
}

#[test]
fn direct_target_tracks_repository_build_and_runtime_file_changes() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[("pkg/defs.bzl", "")])?;
    let repository = BazelRepository::new(&db, root.clone());
    let label = "//pkg:defs.bzl";
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label).err(),
        Some(BazelLoadError::InvalidRepository)
    );

    let marker = root.join("MODULE.bazel");
    db.write_file(&marker, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label).err(),
        Some(BazelLoadError::UnknownTargetPackage)
    );
    let build = root.join("pkg/BUILD");
    db.write_file(&build, "")?;
    let runtime = root.join("pkg/defs.bzl");
    let repository = BazelRepository::new(&db, root.clone());
    let original = resolve_bazel_target(&db, repository, None, label)?;
    let runtime_file = original.selected_file(&db);
    assert_eq!(runtime_file.path(&db), &runtime);

    db.memory_file_system().remove_file(&runtime)?;
    File::sync_path(&mut db, &runtime);
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label).err(),
        Some(BazelLoadError::NotFound)
    );
    db.write_file(&runtime, "")?;
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label)?.selected_file(&db),
        runtime_file
    );

    db.memory_file_system().remove_file(&build)?;
    File::sync_path(&mut db, &build);
    let repository = BazelRepository::new(&db, root.clone());
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label).err(),
        Some(BazelLoadError::UnknownTargetPackage)
    );
    db.memory_file_system().remove_file(&marker)?;
    File::sync_path(&mut db, &marker);
    let repository = BazelRepository::new(&db, root);
    assert_eq!(
        resolve_bazel_target(&db, repository, None, label).err(),
        Some(BazelLoadError::InvalidRepository)
    );
    Ok(())
}
