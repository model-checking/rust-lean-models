import Lake
open Lake DSL

package «rust-lean-models» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "0f3e143"

@[default_target]
lean_lib «RustLeanModels» where
  -- add any library configuration options here
