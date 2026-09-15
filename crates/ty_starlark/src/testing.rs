use ruff_db::Db as _;
use ruff_db::files::{FileRootKind, Files};
use ruff_db::system::{
    DbWithTestSystem as _, DbWithWritableSystem as _, System, SystemPathBuf, TestSystem,
};
use ruff_db::vendored::VendoredFileSystem;

#[salsa::db]
#[derive(Clone, Default)]
pub(crate) struct TestDb {
    storage: salsa::Storage<Self>,
    files: Files,
    system: TestSystem,
    vendored: VendoredFileSystem,
}

#[salsa::db]
impl ruff_db::Db for TestDb {
    fn vendored(&self) -> &VendoredFileSystem {
        &self.vendored
    }

    fn system(&self) -> &dyn System {
        &self.system
    }

    fn files(&self) -> &Files {
        &self.files
    }
}

impl ruff_db::system::DbWithTestSystem for TestDb {
    fn test_system(&self) -> &TestSystem {
        &self.system
    }

    fn test_system_mut(&mut self) -> &mut TestSystem {
        &mut self.system
    }
}

#[salsa::db]
impl salsa::Database for TestDb {}

pub(crate) fn test_db(files: &[(&str, &str)]) -> anyhow::Result<(TestDb, SystemPathBuf)> {
    let mut db = TestDb::default();
    let root = SystemPathBuf::from(if cfg!(windows) { "C:/src" } else { "/src" });
    db.memory_file_system().create_directory_all(&root)?;
    db.files().try_add_root(&db, &root, FileRootKind::Project);
    for (path, contents) in files {
        db.write_file(root.join(path), contents)?;
    }
    Ok((db, root))
}
