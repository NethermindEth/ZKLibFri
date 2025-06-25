import Lake

open System Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.19.0"

require auto from git
  "https://github.com/leanprover-community/lean-auto/"@"v4.19.0"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git"@"5d35ecc273cb1f8344b23f6d23dd69f33601ed31"

package scratch where version := v!"0.1.0"

lean_lib Scratch

@[default_target] lean_exe scratch where root := `Main
                                         supportInterpreter := true
