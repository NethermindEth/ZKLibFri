/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import ArkLib.Data.CodingTheory.BivariatePoly
import Mathlib.Data.Fintype.Defs


open Classical
open Polynomial
open Polynomial.Bivariate

namespace PolishchukSpielman

noncomputable section

variable {F : Type} [Semiring F]
         (m n : ℕ)
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])


lemma existence_of_bivariate_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : Bivariate.setUnivQuotientX a₂ b₂ P₂ f g)
  (h_quot_Y : Bivariate.setUnivQuotientY a₁ b₁ P₁ f g)
  : ∃ q : F[X][Y], g = q * f := sorry


lemma properties_of_bivariate_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ) (q : F[X][Y])
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : Bivariate.setUnivQuotientX a₂ b₂ P₂ f g)
  (h_quot_Y : Bivariate.setUnivQuotientY a₁ b₁ P₁ f g)
  (h_quot_XY : g = q * f) :
  ∃ P₃ : Finset F, P₃.card ≥ n₁ - a₁
  ∧ Bivariate.setUnivQuotientY a₁ b₁ P₃ f g
  ∧ ∃ P₄ : Finset F, P₄.card ≥ n₂ - a₂ ∧ Bivariate.setUnivQuotientY a₂ b₂ P₄ f g
  := by sorry

end
end PolishchukSpielman
