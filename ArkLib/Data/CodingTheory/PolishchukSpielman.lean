/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

<<<<<<< HEAD
import ArkLib.Data.Polynomial.Bivariate

open Polynomial.Bivariate Polynomial

/--
Polishchuk-Spielman Lemma variant from Ben-Sasson et Al. Proximity Gaps for Reed-Solomon Codes
-/
lemma Polishchuk_Spielman {F : Type} [Semiring F] [Field F]
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (f g : F[X][Y]) (a_x a_y b_x b_y n_x n_y : ℕ)
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (h_f_degX : a_x ≥ Bivariate.degreeX f) (h_g_degX : b_x ≥ Bivariate.degreeX g)
  (h_f_degY : a_y ≥ Bivariate.degreeY f) (h_g_degY : b_y ≥ Bivariate.degreeY g)
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_le_1 : (1 : ℚ) > b_x / n_x + b_y / n_y)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧ Bivariate.evalY y g = (quot_X y) * (Bivariate.evalY y f))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧ Bivariate.evalX x g = (quot_Y x) * (Bivariate.evalX x f))
  : ∃ q : F[X][Y], g = q * f
    ∧ Bivariate.degreeX q ≤ b_x - a_x ∧ Bivariate.degreeY q ≤ b_y - a_y
    ∧ (∃ Q_x : Finset F, Q_x.card ≥ n_x - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Bivariate.evalX x q = quot_Y x)
    ∧ (∃ Q_y : Finset F, Q_y.card ≥ n_y - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Bivariate.evalX y q = quot_X y)
    := by
  sorry
=======
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
  (ha₁b₁ : b₁ ≥ a₁) (ha₂b₂ : b₂ ≥ a₂)
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : Bivariate.setUnivQuotientX b₂ a₂ P₂ f g ha₂b₂)
  (h_quot_Y : Bivariate.setUnivQuotientY b₁ a₁ P₁ f g ha₁b₁)
  : ∃ q : F[X][Y], g = q * f := sorry


lemma properties_of_bivariate_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (ha₁b₁ : b₁ ≥ a₁) (ha₂b₂ : b₂ ≥ a₂) (q : F[X][Y])
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : Bivariate.setUnivQuotientX b₂ a₂ P₂ f g ha₂b₂)
  (h_quot_Y : Bivariate.setUnivQuotientY b₁ a₁ P₁ f g ha₁b₁)
  (h_quot_XY : g = q * f) :
  ∃ P₃ : Finset F, P₃.card ≥ n₁ - a₁
  ∧ Bivariate.setUnivQuotientY b₁ a₁ P₃ f g ha₁b₁
  ∧ ∃ P₄ : Finset F, P₄.card ≥ n₂ - a₂ ∧ Bivariate.setUnivQuotientY b₂ a₂ P₄ f g ha₂b₂
  := by sorry

end
end PolishchukSpielman
>>>>>>> 1d27a89 (split filest)
