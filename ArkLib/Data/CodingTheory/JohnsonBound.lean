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
  sqrt_well_def : 0 ≤ 1 - q/(q-1) * δ 
  johnson : ↑q * (↑q - 1) * (2 * ρ - δ) < (↑q * ρ) ^ 2 

noncomputable def J (q : ℕ) (δ : ℚ) : ℝ :=
  (1 - 1/q) * (1 - √(1 - q * δ / (q - 1))) 

lemma under_jonhson_bound_iff_lt_bound {q : ℕ} {ρ δ : ℚ} :
  UnderJohnsonBound q ρ δ ↔ 0 ≤ δ ∧ δ ≤ 1 - 1/q ∧ 2 ≤ q ∧ 0 ≤ 1 - q/(q-1) * δ ∧ ρ < J q δ := by 
  unfold J
  apply Iff.intro
  · rintro ⟨δ_0, δ_u, q_2, sqrt_well_def, johnson⟩
    aesop (config := {warnOnNonterminal := false})
    have h_q : ((1 - (↑q)⁻¹):ℝ) = (q - 1)/q := by
      field_simp
    rw [h_q]
    have h_q : ((↑q - 1)/↑q : ℝ) = ((↑q : ℝ)/(↑q -1))⁻¹ := by 
     field_simp 
    rw [h_q]
    have h_0_le_q : 0 < (↑q : ℝ)/(↑q -1) := by 
      field_simp
      apply lt_of_lt_of_le (by field_simp) q_2
    suffices h : (q/(q-1)) * ρ < (1 - √(1 - ↑q * ↑δ / (↑q - 1))) by {
      sorry 
    }
    suffices h : ↑√(1 - ↑q * ↑δ / (↑q - 1)) < 1 - (↑q : ℝ)/ (↑q - 1) * ↑ρ by {
      sorry 
    }
    suffices h : (1 - (↑q * ↑δ : ℝ) / (↑q - 1)) < (1 - ↑q / (↑q - 1) * ↑ρ) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q - 1 - (↑q * ↑δ : ℝ)) / (↑q - 1)) < ((↑q - 1 - ↑q * ρ) / (↑q - 1)) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q - 1 - (↑q * ↑δ : ℝ)) * (↑q - 1)) < ((↑q - 1 - ↑q * ρ)) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q : ℝ)- 1)^2 - ↑q * (↑q - 1) * ↑δ < (↑q - 1)^2 
        - 2 * ↑q * (↑q - 1) * ↑ρ + (↑q * ρ) ^ 2 by {
      sorry
    }
    suffices h : - ↑q * (↑q - 1) * ↑δ < 
        - 2 * ↑q * (↑q - 1) * ↑ρ + (↑q * ρ) ^ 2 by {
      sorry
    }
    suffices h : 2 * ↑q * (↑q - 1) * ↑ρ - ↑q * (↑q - 1) * ↑δ < (↑q * ρ) ^ 2 by {
      sorry
    }
    -- should follow from johnson at this point.
    sorry
  · rintro ⟨δ_0, δ_u, q_2, sqrt_well_def, johnson⟩  
    exact ⟨by aesop, by aesop, by aesop,by aesop,by {
      -- This should be obtained by reverting the steps in the previous clause
      -- but let's see how that goes :)
      sorry
    }⟩

end JohnsonBound

