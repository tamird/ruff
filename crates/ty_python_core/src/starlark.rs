//! Host-resolved Starlark modules. Label resolution and syntax admission belong
//! to the frontend; semantic queries consume these tracked inputs.

use ruff_db::files::File;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::{Ranged, TextRange};

use crate::Db;

/// A logical module instance, which may share its source with another instance.
///
/// Frontends reuse this identity for repeated loads of the same module. Source
/// and load updates invalidate dependent semantic queries through Salsa.
/// The physical file is fixed for an instance: update its contents or loads,
/// and allocate a new module when changing the physical source. `ProgramFile`
/// caches the parser identity derived from that file.
#[salsa::input(debug)]
pub struct StarlarkModule {
    #[returns(copy)]
    pub file: File,
    #[returns(ref)]
    pub name: Name,
    #[returns(ref)]
    pub loads: Box<[StarlarkLoad]>,
}

impl get_size2::GetSize for StarlarkModule {}

impl StarlarkModule {
    pub fn resolve_load(self, db: &dyn Db, range: TextRange) -> Option<Self> {
        self.loads(db)
            .iter()
            .find(|load| load.range == range)
            .map(|load| load.module)
    }
}

/// A load resolved by the frontend, anchored to its original call expression.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize)]
pub struct StarlarkLoad {
    pub range: TextRange,
    pub module: StarlarkModule,
}

/// A binding in an admitted load. The string retains the exported name and the
/// definition key; the target range points to the alias when one is present.
#[derive(Clone, Copy, Debug)]
pub struct StarlarkLoadBinding<'ast> {
    pub name: &'ast ast::ExprStringLiteral,
    pub alias: Option<&'ast ast::Identifier>,
}

impl StarlarkLoadBinding<'_> {
    pub fn local_name(self) -> Name {
        let Self { name, alias } = self;
        alias.map_or_else(|| Name::new(name.value.to_str()), |alias| alias.id.clone())
    }

    pub fn target_range(self) -> TextRange {
        let Self { name, alias } = self;
        alias.map_or_else(|| name.range(), Ranged::range)
    }
}

/// Iterates bindings after the frontend has admitted the load's syntax.
pub fn load_bindings(call: &ast::ExprCall) -> impl Iterator<Item = StarlarkLoadBinding<'_>> {
    call.arguments
        .args
        .iter()
        .skip(1)
        .filter_map(|argument| {
            Some(StarlarkLoadBinding {
                name: argument.as_string_literal_expr()?,
                alias: None,
            })
        })
        .chain(call.arguments.keywords.iter().filter_map(|keyword| {
            Some(StarlarkLoadBinding {
                name: keyword.value.as_string_literal_expr()?,
                alias: keyword.arg.as_ref(),
            })
        }))
}

pub fn load_call(expression: &ast::Expr) -> Option<&ast::ExprCall> {
    let call = expression.as_call_expr()?;
    call.func.as_name_expr().filter(|name| name.id == "load")?;
    Some(call)
}
