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
def coeffsOfPolynomialBiv (deg : ℕ) (f : F[X][Y]) : Fin deg → F[X] :=
fun ⟨y, _⟩ ↦ Polynomial.coeff f y

lemma natDegreeBiv_lt_of_lbounded_zero_coeff {f : F[X][Y]} {deg : ℕ} [NeZero deg]
  (h : ∀ i, deg ≤ i → f.coeff i = 0) : f.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h f.natDegree)])

/--
Construct a bivariate polynomial in `X` and `Y` from a vector of coefficients,
which are polynomials in `X`.
-/
def polynomialOfCoeffsBiv {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F[X]) : F[X][Y] :=
 ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi a))
                     (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
  ⟩

@[simp]
lemma natDegree_polynomialOfCoeffsBiv_deg_lt_deg {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsBiv coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffsBiv)
        (add safe apply natDegreeBiv_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffsBiv_deg_lt_deg
  {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsBiv coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffsBiv, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffsBiv_eq_coeffs {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsBiv coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffsBiv)

lemma coeff_polynomialOfCoeffsBiv_eq_coeffs' {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsBiv coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffsBiv)

@[simp]
lemma polynomialOfCoeffsBiv_mem_degreeLT {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  polynomialOfCoeffsBiv coeffs ∈ degreeLT F[X] deg := by
  aesop (add simp Polynomial.mem_degreeLT)


@[simp]
lemma polynomialOfCoeffsBiv_eq_zero {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  polynomialOfCoeffsBiv coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffsBiv, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffsBiv_coeffsOfPolynomialBiv {deg : ℕ} [NeZero deg] {f : F[X][Y]}
  (h : f.natDegree + 1 = deg) : polynomialOfCoeffsBiv (coeffsOfPolynomialBiv (deg := deg) f) = f :=
  by
  ext x; symm
  aesop (add simp [polynomialOfCoeffsBiv, coeffsOfPolynomialBiv, coeff_polynomialOfCoeffsBiv_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))
  sorry

@[simp]
lemma coeffsOfPolynomialBiv_polynomialOfCoeffsBiv {deg : ℕ} [NeZero deg]
  {coeffs : Fin deg → F[X]} : coeffsOfPolynomialBiv deg (polynomialOfCoeffsBiv coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [
      polynomialOfCoeffsBiv, coeffsOfPolynomialBiv, coeff_polynomialOfCoeffsBiv_eq_coeffs'
                   ])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
  (polynomialOfCoeffsBiv coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

--@[simp]
--lemma eval_polynomialsOfCoeffsBiv {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} {α : F} :
  ---(polynomialOfCoeffsBiv coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  --simp [eval_eq_sum, sum_def, coeff_polynomialOfCoeffs_eq_coeffs']

def vectorOfEvals {deg : ℕ} [NeZero deg] (a : F) (v : Fin deg → F[X]) : Fin deg → F :=
  fun i ↦ Polynomial.eval a (v i)

def vectorOfEvalsAtX (deg : ℕ) [NeZero deg] (a : F) (f : F[X][Y]) : Fin deg → F :=
 vectorOfEvals a (coeffsOfPolynomialBiv deg f)

def evalAtX (deg : ℕ) [NeZero deg] (a : F) (f : F[X][Y]) : Polynomial F :=
 ReedSolomonCode.polynomialOfCoeffs (vectorOfEvalsAtX (deg := deg) a f)

def evalAtXOnASet (deg : ℕ) [NeZero deg] (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
 { g : Polynomial F | ∃ a ∈ P, evalAtX deg a f = g }

def evalAtY (a : F) (f : F [X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

def evalAtYOnASet (deg : ℕ) [NeZero deg] (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
 { g : Polynomial F | ∃ a ∈ P, evalAtY a f = g }

def degreesXVector (deg : ℕ) (f : F[X][Y]) : Fin deg → ℕ :=
 fun i ↦ Polynomial.natDegree ((coeffsOfPolynomialBiv deg f) i)

def degreesVecToFinset {deg : ℕ} (v : Fin deg → ℕ) : Finset ℕ :=
  Finset.image v Finset.univ

def degreesXFinset (deg : ℕ) (f : F[X][Y]) : Finset ℕ :=
  degreesVecToFinset (degreesXVector (deg := deg) f)


lemma degreesXFinset_nonempty (deg : ℕ) [NeZero deg] (f : F[X][Y]) (h : f ≠ 0) :
 (degreesXFinset deg f).Nonempty := by
 rw [degreesXFinset, degreesVecToFinset]
 unfold degreesXVector
 simp

def degreeX (deg : ℕ) [NeZero deg] (f : F[X][Y]) (h : f ≠ 0) : ℕ :=
(degreesXFinset deg f).max' (degreesXFinset_nonempty deg f h)

def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

def quotientPolyAtX (deg : ℕ) [NeZero deg] (a : F) (f g : F[X][Y]) : Prop :=
  ∃ p : Polynomial F, evalAtX deg a g = p * (evalAtX deg a f)

end

noncomputable section

variable {F : Type*}[Semiring F]
         (deg₁ deg₂ m n : ℕ) [NeZero deg₁] [NeZero deg₂]
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])



def quotientPolyAtXDegBd (hf' : f ≠ 0) (hg' : g ≠ 0)
  (hm : m ≥ degreeX deg₂ g hg') (hn : n ≥ degreeX deg₁ f hf')
  : Prop := ∃ p, p.natDegree ≤ m - n ∧ evalAtX deg₂ a g = p * (evalAtX deg₁ a f)

 --Set (Polynomial F) := { p : Polynomial F | p.natDegree ≤ m - n ∧ evalAtX deg₂ a g = p * (evalAtX deg₁ a f)}

def quotientPolyAtXDegBdSet (hf' : f ≠ 0) (hg' : g ≠ 0)
  (hm : m ≥ degreeX deg₂ g hg') (hn : n ≥ degreeX deg₁ f hf')
  : Set (Polynomial F) :=
  {p : Polynomial F | ∀ a ∈ P, p.natDegree ≤ m - n ∧ evalAtX deg₂ a g = p * (evalAtX deg₁ a f)}

-- def quotientPolyAtXDegBdSetCard (hf' : f ≠ 0) (hg' : g ≠ 0)
--   (hm : m ≥ degreeX deg₂ g hg') (hn : n ≥ degreeX deg₁ f hf')
--   : ℕ := (quotientPolyAtXDegBdSet deg₁ deg₂ m n P f g hf' hg' hm hn).ncard

-- lemma quotientPolyAtXDegBdSetCard_finite
--   [Finite F] (hf' : f ≠ 0) (hg' : g ≠ 0)
--   (hm : m ≥ degreeX deg₂ g hg') (hn : n ≥ degreeX deg₁ f hf') :
--   (quotientPolyAtXDegBdSet deg₁ deg₂ m n P f g hf' hg' hm hn).Finite :=
--   by
--   sorry

def quotientPolyAtY : Prop := ∃ p : Polynomial F, evalAtY a g = p * (evalAtY a f)

def quotientPolyAtYDegBd (hg : m ≥ degreeY g) (hf : n ≥ degreeY f) : Prop
  := ∃ p : Polynomial F, p.natDegree ≤ m - n ∧ evalAtY a g = p * (evalAtY a f)

-- def quotientPolyAtYDegBdSet (hg : m ≥ degreeY g) (hf : n ≥ degreeY f) : Set (Polynomial F)
--  := {p | ∀ a ∈ P, p.natDegree ≤ m - n ∧ evalAtY a g = p * (evalAtY a f)}

-- def quotientPolyAtYDegBdOverSet (hg : m ≥ degreeY g) (hf : n ≥ degreeY f) : Prop :=
--  ∀ a ∈ P, ∃ p_a : Polynomial F, p_a.natDegree ≤ m - n ∧ evalAtY a g = p_a * (evalAtY a f)

 def quotientPolyAtYDegBdOverSet (hg : m ≥ degreeY g) (hf : n ≥ degreeY f) : Prop :=
  ∀ θ ∈ P, quotientPolyAtYDegBd m n θ f g hg hf


-- def quotientPolyAtYDegBdSetCard (hg : m ≥ degreeY g) (hf : n ≥ degreeY f) : ℕ
--   := (quotientPolyAtYDegBdSet m n P f g hg hf).ncard

-- lemma quotientPolyAtYDegBdSetCard_finite [Finite F] (hg : m ≥ degreeY g) (hf : n ≥ degreeY f)
--   : (quotientPolyAtYDegBdSet m n P f g hg hf).Finite := sorry

lemma Polishchuk_Spielman_existence_of_quotients [Field F] [Finite F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (fdegX : a₁ ≥ degreeX deg₁ f hf) (gdegX : b₁ ≥ degreeX deg₂ g hg)
  (fdegY : a₂ ≥ degreeY f) (gdegY : b₂ ≥ degreeY g)
  (hP₁ : n₁ ≥ P₁.card) (hP₂ : n₂ ≥ P₂.card) :
   := sorry

lemma Polishchuk_Spielman_existence_of_global_quotient [Field F] [Finite F] (a₁ a₂ b₁ b₂ n₁ n₂ : ℕ)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (fdegX : a₁ ≥ degreeX deg₁ f hf) (gdegX : b₁ ≥ degreeX deg₂ g hg)
  (fdegY : a₂ ≥ degreeY f) (gdegY : b₂ ≥ degreeY g)
  (hP₁ : n₁ ≥ P₁.card) (hP₂ : n₂ ≥ P₂.card)
   : ∃ quotientPolyAtYDegBdSet a₁ b₁ P₁ f g hg hf ∧

  ∃ q : F[X][Y], g = q * f := sorry

---lemma Polishchuk_Spielman_deg_properties_of_quotient

end
end Bivariate
