/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Fin.Basic

section

open Fin

variable {F : Type} [DecidableEq F]
variable {n : ℕ}

/-- This should be gone once min distance is merged -/
lemma an_implication_of_min_dist {k : ℕ} [Field F] {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj: Function.Injective ωs) 
  (h_dist : Δ₀((fun a ↦ Polynomial.eval a p) ∘ ωs, 0) < n - k + 1)
  : p = 0 := by
  by_cases hk : k = 0
  · simp [hk] at h_deg
  · have h_n_k_1 : n - k + 1 = n - (k - 1) := by omega
    rw [h_n_k_1] at h_dist 
    simp [hammingDist] at *
    rw [←Finset.compl_filter, Finset.card_compl] at h_dist
    simp at h_dist 
    have hk : 1 ≤ k := by omega
    rw [←Finset.card_image_of_injective _ h_inj 
    ] at h_dist
    have h_dist_p : k  ≤ 
      (@Finset.image (Fin n) F _ ωs {i | Polynomial.eval (ωs i) p = 0} : Finset F).card 
        := by omega
    by_cases heq_0 : p = 0 <;> try simp [heq_0]
    have h_dist := Nat.le_trans h_dist_p (by {
      apply Polynomial.card_le_degree_of_subset_roots (p := p)
      intro x hx 
      aesop
    })
    omega

end
