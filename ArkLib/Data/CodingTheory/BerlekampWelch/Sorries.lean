/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Matrix.Mul 

variable {α : Type} {F : Type} [Field F]
variable {n m : ℕ}

opaque linsolve (A : Matrix (Fin n) (Fin m) F) (b : Fin n → F) : Option (Fin m → F)
  := sorry 

theorem linsolve_some {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} {x : Fin m → F}
  (h : linsolve A b = some x)
  : A.mulVec x = b := sorry 

theorem linsolve_none {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} 
  (h : linsolve A b = none)
  : ¬∃ x, A.mulVec x = b := by sorry

