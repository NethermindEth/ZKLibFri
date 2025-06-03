/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import ArkLib.Data.CodingTheory.ReedSolomonCodes
import Mathlib.Data.Fintype.Defs


open Classical
open Polynomial
open Polynomial.Bivariate

namespace Bivariate

noncomputable section

variable {F : Type*}[Semiring F]

/--
The vector of coefficients of a bivariate polynomial.
-/
def coeffsOfBivPolynomial (deg : ℕ) (f : F[X][Y]) : Fin deg → F[X] :=
fun ⟨y, _⟩ ↦ Polynomial.coeff f y

lemma natDegreeBiv_lt_of_lbounded_zero_coeff {f : F[X][Y]} {deg : ℕ} [NeZero deg]
  (h : ∀ i, deg ≤ i → f.coeff i = 0) : f.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h f.natDegree)])

/--
Construct a bivariate polynomial in `X` and `Y` from a vector of coefficients,
which are polynomials in `X`.
-/
def polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F[X]) : F[X][Y] :=
 ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi a))
                     (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
  ⟩

@[simp]
lemma natDegree_polynomialOfCoeffsOfBiv_deg_lt_deg {deg : ℕ} [NeZero deg]
(coeffs : Fin deg → F[X]) :
  (polynomialOfCoeffsOfBiv coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffsOfBiv)
        (add safe apply natDegreeBiv_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffsOfBiv_deg_lt_deg
  {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsOfBiv coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffsOfBiv, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsOfBiv coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffsOfBiv)

lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs' {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsOfBiv coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffsOfBiv)

@[simp]
lemma polynomialOfCoeffsOfBiv_mem_degreeLT {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  polynomialOfCoeffsOfBiv coeffs ∈ degreeLT F[X] deg := by
  aesop (add simp Polynomial.mem_degreeLT)


@[simp]
lemma polynomialOfCoeffsOfBiv_eq_zero {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  polynomialOfCoeffsOfBiv coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffsOfBiv, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffsBiv_coeffsOfPolynomialBiv (deg : ℕ) [NeZero deg]
  {f : F[X][Y]} (h : f.natDegree + 1 = deg)
  : polynomialOfCoeffsOfBiv (coeffsOfBivPolynomial deg f) = f := by sorry
  -- ext x; symm
  -- aesop (add simp [polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'])
  --       (add safe apply coeff_eq_zero_of_natDegree_lt)
  --       (add safe (by omega))


@[simp]
lemma coeffsOfBivPolynomial_polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg]
  {coeffs : Fin deg → F[X]} : coeffsOfBivPolynomial deg (polynomialOfCoeffsOfBiv coeffs) = coeffs
  := by
  ext x; symm
  aesop (add simp [
      polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'
                   ])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfBivCoeffs (deg : ℕ) [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsOfBiv coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

/--
The vector of evaluations of a polynomial at a given point.
-/
def vectorOfEvals {deg : ℕ} [NeZero deg] (a : F) (v : Fin deg → F[X]) : Fin deg → F :=
  fun i ↦ Polynomial.eval a (v i)

/--
The vector of evaluations in the first variable `X` of a bivariate polynomial at a given point.
-/
def vectorOfEvalsAtX (deg : ℕ) [NeZero deg] (a : F) (f : F[X][Y]) : Fin deg → F :=
  vectorOfEvals a (coeffsOfBivPolynomial deg f)

/--
The evaluation of a bivariate polynomial in the first variable `X` at a point
given as a univariate polynomial in the second variable `Y`.
-/
def evalAtX (deg : ℕ) [NeZero deg] (a : F) (f : F[X][Y]) : Polynomial F :=
  ReedSolomonCode.polynomialOfCoeffs (vectorOfEvalsAtX deg a f)

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points resulting in a set of
univariate polynomials in `Y`.
-/
def evalAtXOnASet (deg : ℕ) [NeZero deg] (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
  {g : Polynomial F | ∃ a ∈ P, evalAtX deg a f = g}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalAtY (a : F) (f : F [X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalAtYOnASet (deg : ℕ) [NeZero deg] (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
  {g : Polynomial F | ∃ a ∈ P, evalAtY a f = g}

/--
The tuple of `X` degrees of a bivariate polynomial.
-/
def degreesXVector (deg : ℕ) (f : F[X][Y]) : Fin deg → ℕ :=
  fun i ↦ Polynomial.natDegree ((coeffsOfBivPolynomial deg f) i)

def degreesVecToFinset {deg : ℕ} (v : Fin deg → ℕ) : Finset ℕ :=
  Finset.image v Finset.univ

/--
`X` degrees of a bivariate polynomial as a Finset.
-/
def degreesXFinset (deg : ℕ) (f : F[X][Y]) : Finset ℕ :=
  degreesVecToFinset (degreesXVector deg f)

/--
The Finset of `X`-degrees of a bivariate polynomial is non-empty.
-/
lemma degreesXFinset_nonempty (deg : ℕ) [NeZero deg] (f : F[X][Y]) (h : f ≠ 0) :
 (degreesXFinset deg f).Nonempty := by
 rw [degreesXFinset, degreesVecToFinset]
 unfold degreesXVector
 simp

/--
The `X` degree of a bivariate polynomial is the maximum of the `X`-degrees of its monomials.
-/
def degreeX (deg : ℕ) [NeZero deg] (f : F[X][Y]) (h : f ≠ 0) : ℕ :=
(degreesXFinset deg f).max' (degreesXFinset_nonempty deg f h)

/--
The `Y` degree of a bivariate polynomial.
-/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

end

noncomputable section

variable {F : Type*}[Semiring F]
         (deg₁ deg₂ m n : ℕ) [NeZero deg₁] [NeZero deg₂]
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])

/--
The quotient univariate polynomial in `Y` obtained after evaluating two bivariate polynomials in `X`
and viewing them as univariate polynomials in `Y`.
-/
def quotientPolyAtY (a : F) : Prop :=
  ∃ p : Polynomial F, evalAtX deg₂ a g = p * (evalAtX deg₁ a f)

def quotientPolyYDeg (hf' : f ≠ 0) (hg' : g ≠ 0) : Prop :=
  ∃ p, p.natDegree ≤ degreeX deg₁ f hf' - degreeX deg₂ g hg'
  ∧ evalAtX deg₂ a g = p * (evalAtX deg₁ a f)

/--
The quotient univariate polynomial in `Y` with a relaxed degree bound.
-/
def quotientPolyYBdDeg (hf' : f ≠ 0) (hg' : g ≠ 0)
  (hm : m ≥ degreeX deg₁ f hf') (hn : n ≥ degreeX deg₂ g hg')
  : Prop := ∃ p, p.natDegree ≤ m - n ∧ evalAtX deg₂ a g = p * (evalAtX deg₁ a f)

 def quotientPolyYBdDegSet (hf' : f ≠ 0) (hg' : g ≠ 0)
 (hm : m ≥ degreeX deg₁ f hf') (hn : n ≥ degreeX deg₂ g hg') : Prop
  := ∀ θ ∈ P, quotientPolyYBdDeg deg₁ deg₂ m n θ f g hf' hg' hm hn


def quotientPolyX : Prop := ∃ p : Polynomial F, evalAtY a g = p * (evalAtY a f)

def quotientPolyXBdDeg (hf : m ≥ degreeY f) (hg : n ≥ degreeY g) : Prop
  := ∃ p : Polynomial F, p.natDegree ≤ m - n ∧ evalAtY a g = p * (evalAtY a f)

def quotientPolyXBdDegSet (hf : m ≥ degreeY f) (hg : n ≥ degreeY g) : Prop :=
  ∀ θ ∈ P, quotientPolyXBdDeg m n θ f g hf hg

lemma Polishchuk_Spielman_existence_of_quotient [Field F] [Finite F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (fdegX : a₁ ≥ degreeX deg₁ f hf) (gdegX : b₁ ≥ degreeX deg₂ g hg)
  (fdegY : a₂ ≥ degreeY f) (gdegY : b₂ ≥ degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : quotientPolyXBdDegSet a₂ b₂ P₂ f g fdegY gdegY)
  (h_quot_Y : quotientPolyYBdDegSet deg₁ deg₂ a₁ b₁ P₁ f g hf hg fdegX gdegX)
  : ∃ q : F[X][Y], g = q * f := sorry

lemma biv_quotient_nezero (q : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by sorry

lemma biv_quotient_Xdeg_bd (q : F[X][Y]) (deg₃ : ℕ) [NeZero deg₃] (hf : f ≠ 0) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) :
  degreeX deg₃ q (biv_quotient_nezero  f g q hf hg h_quot_XY) ≤ degreeX deg₂ g hg - degreeX deg₁ f hf
  := by sorry

lemma biv_quotient_Ydeg_bd (q : F[X][Y]) (deg₃ : ℕ) [NeZero deg₃] (hf : f ≠ 0) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) : degreeY q  ≤ degreeY g - degreeY f  := by sorry

lemma Polishchuk_Spielman_eval_prop_quotient [Field F][Finite F] (a₁ a₂ b₁ b₂ n₁ n₂ deg₃ : ℕ)
  [NeZero deg₃] (q : F[X][Y])
  (hf : f ≠ 0) (hg : g ≠ 0) (hq : q ≠ 0)
  (fdegX : a₁ ≥ degreeX deg₁ f hf) (gdegX : b₁ ≥ degreeX deg₂ g hg)
  (fdegY : a₂ ≥ degreeY f) (gdegY : b₂ ≥ degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : quotientPolyXBdDegSet a₂ b₂ P₂ f g fdegY gdegY)
  (h_quot_Y : quotientPolyYBdDegSet deg₁ deg₂ a₁ b₁ P₁ f g hf hg fdegX gdegX)
  (h_quot_XY : g = q * f) :
  ∃ P₃ : Finset F, P₃.card ≥ n₁ - a₁
  ∧ quotientPolyYBdDegSet deg₁ deg₂ a₁ b₁ P₃ f g hf hg fdegX gdegX
  ∧ ∃ P₄ :Finset F, P₄.card ≥ n₂ - a₂ ∧ quotientPolyXBdDegSet a₂ b₂ P₄ f g fdegY gdegY := sorry

end
end Bivariate
