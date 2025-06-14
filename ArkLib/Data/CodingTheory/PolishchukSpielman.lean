/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.BivariatePoly

open Polynomial.Bivariate

namespace PolishchukSpielman

noncomputable section

variable {F : Type} [Semiring F]
         (m n : ℕ)
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])

/--
The quotient univariate polynomial in `Y` obtained after evaluating bivariate polynomials
`f` and `g` in `X` at a point and dividing in the ring `F[Y]`.
-/
def quotientPolyYAfterEvalX : Prop :=
  ∃ p : Polynomial F, Bivariate.evalX a g = p * (Bivariate.evalX a f)

/--
Given two integers, we form a tighter degree bound on the quotient polynomial in `Y` obtained after
evaluating in `X`.
-/
def quotientPolyYAfterEvalX_degBd : Prop :=
  ∃ p, p.natDegree ≤ m - n ∧ Bivariate.evalX a g = p * (Bivariate.evalX a f)

/--
The set of univariate quotients in `Y` obtained after evaluating `X` on a given set of points.
-/
def setOfQuotientPolyYAfterEvalX : Prop :=
  ∀ θ ∈ P, quotientPolyYAfterEvalX_degBd m n θ f g

/--
The quotient univariate polynomial in `X` obtained after evaluating bivariate polynomials
`f` and `g` in `Y` at a point and dividing in the ring `F[X]`.
-/
def quotientPolyXAfterEvalY : Prop :=
  ∃ p : Polynomial F, Bivariate.evalY a g = p * (Bivariate.evalY a f)

/--
Given two integers, we form a tighter degree bound on the quotient polynomial in `X` obtained after
evaluating in `Y`.
-/
def quotientPolyXAfterEvalY_degBd : Prop :=
  ∃ p : Polynomial F, p.natDegree ≤ m - n ∧ Bivariate.evalY a g = p * (Bivariate.evalY a f)

/--
The set of univariate quotients in `X` obtained after evaluating `Y` on a given set of points.
-/
def setOfQuotientPolyXAfterEvalY : Prop :=
  ∀ θ ∈ P, quotientPolyXAfterEvalY_degBd m n θ f g

/--
Polishchuk-Spielman Lemma, existence part : If all conditions below are satisfied, then there exists
a bivariate quotient of the given bivariate polynomials `f` and `g`. The `X` and `Y` degrees of the
quotient satisfy given bounds too.
-/
lemma existence_of_bivariate_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (ha₁b₁ : b₁ ≥ a₁) (ha₂b₂ : b₂ ≥ a₂)
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > (b₁ : ℚ)/(P₁.card : ℚ) + (b₂ : ℚ)/(P₂.card : ℚ))
  (h_quot_X : setOfQuotientPolyXAfterEvalY b₂ a₂ P₂ f g)
  (h_quot_Y : setOfQuotientPolyYAfterEvalX b₁ a₁ P₁ f g)
  : ∃ q : F[X][Y], g = q * f
    ∧ Bivariate.degreeX q ≤ b₁ - a₁ ∧ Bivariate.degreeY q ≤ b₂ - a₂ := sorry

/--
Polishchuk-Spielman Lemma, properties of the bivariate quotient: If the bivariate quotient exists,
then it is consistent on a certain number of points with the univariate quotients
obtained after evaluating in `X` and `Y` respectively.
-/
lemma properties_of_bivariate_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (ha₁b₁ : b₁ ≥ a₁) (ha₂b₂ : b₂ ≥ a₂) (q : F[X][Y])
  (h_f_degX : a₁ ≥ Bivariate.degreeX f) (h_g_degX : b₁ ≥ Bivariate.degreeX g)
  (h_f_degY : a₂ ≥ Bivariate.degreeY f) (h_g_degY : b₂ ≥ Bivariate.degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > (b₁ : ℚ)/(P₁.card : ℚ) + (b₂ : ℚ) /(P₂.card : ℚ))
  (h_quot_X : setOfQuotientPolyXAfterEvalY b₂ a₂ P₂ f g)
  (h_quot_Y : setOfQuotientPolyYAfterEvalX b₁ a₁ P₁ f g)
  (h_quot_XY : g = q * f) :
  ∃ P₃ : Finset F, P₃.card ≥ n₁ - a₁
  ∧ setOfQuotientPolyYAfterEvalX b₁ a₁ P₃ f g
  ∧ ∃ P₄ : Finset F, P₄.card ≥ n₂ - a₂ ∧ setOfQuotientPolyYAfterEvalX b₂ a₂ P₄ f g
  := by sorry


end
end PolishchukSpielman
