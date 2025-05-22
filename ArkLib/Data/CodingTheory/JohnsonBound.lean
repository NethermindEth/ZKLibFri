/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov 
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic

namespace JohnsonBound

structure UnderJohnsonBound (q : ℕ) (ρ δ : ℚ)  : Prop where 
  δ_0 : 0 ≤ δ 
  δ_u : δ ≤ 1 - 1/q 
  q_2 : 2 ≤ q 
  ρ_pos : 0 ≤ 1 - q/(q-1) * ρ 
  johnson : 0 ≤ q * q * (ρ - δ) - q * (δ - 2 * ρ) 

noncomputable def J (q : ℕ) (δ : ℚ) : ℝ :=
  (1 - 1/q) * (1 - √(1 - q * δ / (q - 1))) 

lemma under_jonhson_bound_iff_le_bound {q : ℕ} {ρ δ : ℚ} :
  UnderJohnsonBound q ρ δ ↔ 0 ≤ δ ∧ δ ≤ 1 - 1/q ∧ 2 ≤ q ∧ 0 ≤ 1 - q/(q-1) * ρ ∧ ρ < J q δ := by 
  /- unfold J -/
  /- apply Iff.intro -/
  /- · rintro ⟨δ_0, δ_u, q_2, ρ_pos, johnson⟩ -/
  /-   have h_q : ((1 - 1/q):ℝ) = (q - 1)/q := by -/
  /-     field_simp -/
  /-   rw [h_q] -/
  /-   suffices h : (q * ρ/(q-1)) < (1 - √(1 - ↑q * ↑δ / (↑q - 1))) by { -/
  /-     so -/
  /-   } -/
  sorry

    

end JohnsonBound

