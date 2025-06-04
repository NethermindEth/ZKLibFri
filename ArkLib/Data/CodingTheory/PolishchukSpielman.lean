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

variable {F : Type} [Semiring F]

/--
The vector of coefficients of a bivariate polynomial, where coefficients are interpreted as
polynomials in the first variable `X`.
-/
def coeffsOfBivPolynomial (f : F[X][Y]) : Fin f.natDegree → F[X] :=
fun ⟨y, _⟩ ↦ Polynomial.coeff f y

-- lemma natDegreeBiv_lt_of_lbounded_zero_coeff {f : F[X][Y]} {deg : ℕ} [NeZero deg]
--   (h : ∀ i, deg ≤ i → f.coeff i = 0) : f.natDegree < deg := by
--   aesop (add unsafe [(by by_contra), (by specialize h f.natDegree)])

-- /--
-- Construct a bivariate polynomial in `X` and `Y` from a vector of coefficients,
-- which are polynomials in `X`.
-- -/
-- def polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F[X]) : F[X][Y] :=
--  ⟨
--     Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
--     fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
--     fun a ↦ by aesop (add safe (by existsi a))
--                      (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
--   ⟩

-- @[simp]
-- lemma natDegree_polynomialOfCoeffsOfBiv_deg_lt_deg {deg : ℕ} [NeZero deg]
-- (coeffs : Fin deg → F[X]) :
--   (polynomialOfCoeffsOfBiv coeffs).natDegree < deg := by
--   aesop (add simp polynomialOfCoeffsOfBiv)
--         (add safe apply natDegreeBiv_lt_of_lbounded_zero_coeff)

-- @[simp]
-- lemma degree_polynomialOfCoeffsOfBiv_deg_lt_deg
--   {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).degree < deg := by
--   aesop (add simp [polynomialOfCoeffsOfBiv, degree_lt_iff_coeff_zero])

-- @[simp]
-- lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
--   aesop (add simp polynomialOfCoeffsOfBiv)

-- lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs' {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
--   aesop (add simp polynomialOfCoeffsOfBiv)

-- @[simp]
-- lemma polynomialOfCoeffsOfBiv_mem_degreeLT {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   polynomialOfCoeffsOfBiv coeffs ∈ degreeLT F[X] deg := by
--   aesop (add simp Polynomial.mem_degreeLT)


-- @[simp]
-- lemma polynomialOfCoeffsOfBiv_eq_zero {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   polynomialOfCoeffsOfBiv coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
--   simp [polynomialOfCoeffsOfBiv, AddMonoidAlgebra.ext_iff]

-- lemma polynomialOfCoeffsBiv_coeffsOfPolynomialBiv (deg : ℕ) [NeZero deg]
--   {f : F[X][Y]} (h : f.natDegree + 1 = deg)
--   : polynomialOfCoeffsOfBiv (coeffsOfBivPolynomial deg f) = f := by sorry
  -- ext x; symm
  -- aesop (add simp [polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'])
  --       (add safe apply coeff_eq_zero_of_natDegree_lt)
  --       (add safe (by omega))


-- @[simp]
-- lemma coeffsOfBivPolynomial_polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg]
--   {coeffs : Fin deg → F[X]} : coeffsOfBivPolynomial deg (polynomialOfCoeffsOfBiv coeffs) = coeffs
--   := by
--   ext x; symm
--   aesop (add simp [
--       polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'
--                    ])
--         (add safe (by omega))

-- @[simp]
-- lemma support_polynomialOfBivCoeffs (deg : ℕ) [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).support =
--   Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

/--
The vector of evaluations of a polynomial at a given point.
-/
-- def vectorOfEvals {deg : ℕ} [NeZero deg] (a : F) (v : Fin deg → F[X]) : Fin deg → F :=
--   fun i ↦ Polynomial.eval a (v i)

--The vector of evaluations in the first variable `X` of a bivariate polynomial at a given point.

-- def vectorOfEvalsAtX (deg : ℕ) [NeZero deg] (a : F) (f : F[X][Y]) : Fin deg → F :=
--   vectorOfEvals a (coeffsOfBivPolynomial deg f)


def evalAtX (a : F) (f : F[X][Y]) : F[X] :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩
  -- ReedSolomonCode.polynomialOfCoeffs (vectorOfEvalsAtX deg a f)

lemma evalAtX_deg_le_degY (a : F) (f : F[X][Y]) :
  (evalAtX a f).natDegree ≤ f.natDegree := by
  sorry

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points resulting in a set of
univariate polynomials in `Y`.
-/
def evalAtXOnASet (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
 {h : Polynomial F | ∃ a ∈ P, evalAtX a f = h}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalAtY (a : F) (f : F [X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalAtYOnASet (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalAtY a f = h}

/--
The tuple of `X` degrees of a bivariate polynomial.
-/
def degreesXVector (f : F[X][Y]) : Fin f.natDegree → ℕ :=
  fun i ↦ Polynomial.natDegree ((coeffsOfBivPolynomial f) i)

-- def degreesXVector (deg : ℕ) (f : F[X][Y]) : Fin deg → ℕ :=
--   fun i ↦ Polynomial.natDegree ((coeffsOfBivPolynomial deg f) i)

def vecToFinset {n: ℕ} (v : Fin n → ℕ) : Finset ℕ :=
  Finset.image v Finset.univ

/--
`X` degrees of a bivariate polynomial as a Finset.
-/
def degreesXFinset (f : F[X][Y]) : Finset ℕ :=
  vecToFinset (degreesXVector f)


/--
The Finset of `X`-degrees of a bivariate polynomial is non-empty.
-/
lemma degreesXFinset_nonempty (f : F[X][Y]) (hf : f ≠ 0) :
 (degreesXFinset f).Nonempty := by
 rw [degreesXFinset, vecToFinset]
 unfold degreesXVector
 simp
 rw [@Finset.univ_nonempty_iff]
 have fdeg : f.natDegree > 0 := by
  sorry

def degreeX' (f : F[X][Y])(hf : f ≠ 0) : ℕ :=
  (degreesXFinset f).max' (degreesXFinset_nonempty f hf)




def degreesXFinset' (f : F[X][Y]) : Finset ℕ :=
  f.toFinsupp.support

lemma degreesXFinset'_nonempty (f : F[X][Y]) (hf: f ≠ 0) : (degreesXFinset' f).Nonempty := by
  rw[degreesXFinset']
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)


def degreesX' (f : F[X][Y]) (hf : f ≠ 0): ℕ :=
  f.toFinsupp.support.max' (degreesXFinset'_nonempty f hf)


--Julian's def
def degreeX (f : F[X][Y]) : ℕ :=
  match f.toFinsupp.support.max with
  | ⊥ => 0
  | .some n => n

/--
The `Y` degree of a bivariate polynomial.
-/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

end

noncomputable section

variable {F : Type} [Semiring F]
         (m n : ℕ)
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])

/--
The quotient univariate polynomial in `Y` obtained after evaluating two bivariate polynomials in `X`
and viewing them as univariate polynomials in `Y`.
-/
def quotientPolyAtY (a : F) : Prop :=
  ∃ p : Polynomial F, evalAtX a g = p * (evalAtX a f)

--example : quotientPolyAtY f g a → ∃ p : Polynomial F, evalAtX a g = p * (evalAtX a f) := id


lemma quotientPolyAtYDeg (p : F[X]) :
  evalAtX a g = p * (evalAtX a f) →
    p.natDegree ≤ degreeX g - degreeX f := by
    sorry

lemma quotientPolyAtY_Deg' (p : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
  evalAtX a g = p * (evalAtX a f) →
    p.natDegree ≤ degreesX' g hg - degreesX' f hf := by
    intro h
    sorry

-- lemma quotientPolyAtY_deg_bd (a₁ b₁ : ℕ) (p : F[X]) (h_ab: b₁ ≥ a₁ ) (h_fg : degreeX f ≤ degreeX g)
--   (h_f_degX : a₁ ≥ degreeX f) (h_g_degX : b₁ ≥ degreeX g) :
--   evalAtX a g = p * (evalAtX a f) →
--     p.natDegree ≤ b₁ - a₁ := by
--     intro h
--     have p_deg : p.natDegree ≤ degreeX g - degreeX f := by sorry
--     simp_all only [ge_iff_le]
--     rw [propext (Nat.le_sub_iff_add_le h_fg)] at p_deg
--     rw [propext (Nat.le_sub_iff_add_le h_ab)]
--     apply le_trans _ h_g_degX
--     rw [← Nat.le_sub_iff_add_le]
--     zify at h_f_degX
--     rw [← neg_le_neg] at h_f_degX


--     have fdeg_neg : - a₁ ≤ - degreeX f := sorry
--     omega

--     exact le_trans (add_le_add_right h_f_degX _) p_deg
--     exact le_trans _ h_g_degX


--     sorry



-- lemma quotientPolyAtY_deg'_bd (p : F[X]) (hf : f ≠ 0) (hg : g ≠ 0)
--   (h_f_degX : a₁ ≥ degreeX f) (h_g_degX : b₁ ≥ degreeX g) :
--   evalAtX a g = p * (evalAtX a f) →
--     p.natDegree ≤ degreesX' f hf - degreesX' g hg := by sorry

-- def quotientPolyYDeg : Prop :=
--   ∃ p, p.natDegree ≤ degreeX f - degreeX g
--   ∧ evalAtX a g = p * (evalAtX a f)


/--
The quotient univariate polynomial in `Y` with a needed degree bound.
-/
def quotientPolyYBdDeg : Prop := ∃ p, p.natDegree ≤ m - n ∧ evalAtX a g = p * (evalAtX a f)

def quotientPolyYBdDegSet : Prop
  := ∀ θ ∈ P, quotientPolyYBdDeg m n θ f g


def quotientPolyX : Prop := ∃ p : Polynomial F, evalAtY a g = p * (evalAtY a f)

def quotientPolyXBdDeg : Prop
  := ∃ p : Polynomial F, p.natDegree ≤ m - n ∧ evalAtY a g = p * (evalAtY a f)

def quotientPolyXBdDegSet : Prop :=
  ∀ θ ∈ P, quotientPolyXBdDeg m n θ f g

lemma Polishchuk_Spielman_existence_of_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (h_f_degX : a₁ ≥ degreeX f) (h_g_degX : b₁ ≥ degreeX g)
  (h_f_degY : a₂ ≥ degreeY f) (h_g_degY : b₂ ≥ degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : quotientPolyXBdDegSet a₂ b₂ P₂ f g)
  (h_quot_Y : quotientPolyYBdDegSet a₁ b₁ P₁ f g)
  : ∃ q : F[X][Y], g = q * f := sorry

lemma biv_quotient_nezero (q : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by sorry

lemma biv_quotient_Xdeg_bd (q : F[X][Y]) (deg₃ : ℕ) [NeZero deg₃] (hf : f ≠ 0) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) :
  degreeX q ≤ degreeX g - degreeX f
  := by sorry

lemma biv_quotient_Ydeg_bd (q : F[X][Y]) (deg₃ : ℕ) [NeZero deg₃] (hf : f ≠ 0) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) : degreeY q  ≤ degreeY g - degreeY f  := by sorry

lemma Polishchuk_Spielman_eval_prop_quotient [Field F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ) (q : F[X][Y])
  (h_f_degX : a₁ ≥ degreeX f) (h_g_degX : b₁ ≥ degreeX g)
  (h_f_degY : a₂ ≥ degreeY f) (h_g_degY : b₂ ≥ degreeY g)
  (h_card_P₁ : n₁ ≥ P₁.card) (h_card_P₂ : n₂ ≥ P₂.card)
  (h_le_1: 1 > b₁/P₁.card + b₂/P₂.card)
  (h_quot_X : quotientPolyXBdDegSet a₂ b₂ P₂ f g)
  (h_quot_Y : quotientPolyYBdDegSet a₁ b₁ P₁ f g)
  (h_quot_XY : g = q * f) :
  ∃ P₃ : Finset F, P₃.card ≥ n₁ - a₁
  ∧ quotientPolyYBdDegSet a₁ b₁ P₃ f g
  ∧ ∃ P₄ : Finset F, P₄.card ≥ n₂ - a₂ ∧ quotientPolyXBdDegSet a₂ b₂ P₄ f g
  := by sorry

end
end Bivariate
