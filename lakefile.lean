import Lake
open Lake DSL

package comm_alg

@[default_target]
lean_lib CommAlg where
  moreLeanArgs := #["-Dpp.unicode.fun=true"] -- pretty-prints `fun a ↦ b`

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
