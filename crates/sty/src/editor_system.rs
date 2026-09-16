//! Editor text overlays Ruff's file system without changing checked file IDs.

use std::any::Any;
use std::sync::Arc;

use ruff_db::FxDashMap;
use ruff_db::file_revision::FileRevision;
use ruff_db::system::walk_directory::WalkDirectoryBuilder;
use ruff_db::system::{
    CommandExecutor, DirectoryEntry, FileType, Metadata, OsSystem, Result, System, SystemPath,
    SystemPathBuf, SystemVirtualPath, WhichResult, WritableSystem,
};
use ruff_notebook::{Notebook, NotebookError};

#[derive(Clone, Debug)]
pub(crate) struct EditorSystem {
    native: OsSystem,
    documents: Arc<FxDashMap<SystemPathBuf, OpenText>>,
}

#[derive(Clone, Debug)]
pub(crate) struct OpenText {
    pub text: String,
    pub revision: u64,
}

impl EditorSystem {
    pub(crate) fn new(cwd: &SystemPath) -> Self {
        Self {
            native: OsSystem::new(cwd),
            documents: Arc::new(FxDashMap::default()),
        }
    }

    pub(crate) fn open(&self, path: SystemPathBuf, document: OpenText) {
        self.documents.insert(path, document);
    }

    pub(crate) fn close(&self, path: &SystemPath) {
        self.documents.remove(path);
    }

    pub(crate) fn text(&self, path: &SystemPath) -> Option<OpenText> {
        self.documents.get(path).map(|entry| entry.value().clone())
    }
}

impl System for EditorSystem {
    fn path_metadata(&self, path: &SystemPath) -> Result<Metadata> {
        if let Some(entry) = self.documents.get(path) {
            return Ok(Metadata::new(
                FileRevision::new(u128::from(entry.revision)),
                None,
                FileType::File,
            ));
        }
        self.native.path_metadata(path)
    }

    fn canonicalize_path(&self, path: &SystemPath) -> Result<SystemPathBuf> {
        self.native.canonicalize_path(path)
    }

    fn is_same_file(&self, first: &SystemPath, second: &SystemPath) -> Result<bool> {
        self.native.is_same_file(first, second)
    }

    fn read_to_string(&self, path: &SystemPath) -> Result<String> {
        if let Some(entry) = self.documents.get(path) {
            return Ok(entry.text.clone());
        }
        self.native.read_to_string(path)
    }

    fn read_to_notebook(&self, path: &SystemPath) -> std::result::Result<Notebook, NotebookError> {
        self.native.read_to_notebook(path)
    }

    fn read_virtual_path_to_string(&self, path: &SystemVirtualPath) -> Result<String> {
        self.native.read_virtual_path_to_string(path)
    }

    fn read_virtual_path_to_notebook(
        &self,
        path: &SystemVirtualPath,
    ) -> std::result::Result<Notebook, NotebookError> {
        self.native.read_virtual_path_to_notebook(path)
    }

    fn which(&self, name: &str) -> WhichResult {
        self.native.which(name)
    }

    fn command_executor(&self) -> Option<&dyn CommandExecutor> {
        self.native.command_executor()
    }

    fn current_directory(&self) -> &SystemPath {
        self.native.current_directory()
    }

    fn user_config_directory(&self) -> Option<SystemPathBuf> {
        self.native.user_config_directory()
    }

    fn cache_dir(&self) -> Option<SystemPathBuf> {
        self.native.cache_dir()
    }

    fn read_directory<'a>(
        &'a self,
        path: &SystemPath,
    ) -> Result<Box<dyn Iterator<Item = Result<DirectoryEntry>> + 'a>> {
        self.native.read_directory(path)
    }

    fn walk_directory(&self, path: &SystemPath) -> WalkDirectoryBuilder {
        self.native.walk_directory(path)
    }

    fn as_writable(&self) -> Option<&dyn WritableSystem> {
        None
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn dyn_clone(&self) -> Box<dyn System> {
        Box::new(self.clone())
    }
}
