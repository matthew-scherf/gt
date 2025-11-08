import Lake
open Lake DSL

package «SubstrateTheory» where
  version := v!"7.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SubstrateTheory» where
  globs := #[.submodules `SubstrateTheory]
