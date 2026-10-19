## What it does

Checks for `ty: ignore` comments that don't specify which rules to ignore. Applications embedding ty
can also require rule codes in `type: ignore` comments and reject file-wide ignore comments.

## Why is this bad?

A blanket `ty: ignore` comment suppresses every type-checking diagnostic on the applicable line or
file. Specifying rule codes documents which diagnostics are expected and prevents the comment from
silencing unrelated errors.

File-wide comments can also hide new errors from a specified rule anywhere in the file. An ignore on
the affected line limits its scope.

## Examples

```py
# error
value = unknown  # ty: ignore
```

Use instead:

```py
value = unknown  # ty: ignore[unresolved-reference]
```
