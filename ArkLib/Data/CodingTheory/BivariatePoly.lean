/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Fintype.Defs

open Classical
open Polynomial
open Polynomial.Bivariate

namespace Bivariate

noncomputable section

variable {F : Type} [Semiring F]
         (a : F)
         (f g : F[X][Y])

/--
The set of coefficients of a bivariate polynomial.
-/
def coeffs : Finset F[X] := f.support.image (fun n => f.coeff n)

/---
The coeffiecient of `Y^n` is a polynomial in `X`.
-/
def coeff_Y_n (n : ℕ) : F[X] := f.coeff n

/--
The `Y`-degree of a bivariate polynomial.
-/
def degreeY : ℕ := Polynomial.natDegree f

-- Katy: The next def, lemma and def can be deleted. Just keeping for now in case we need
-- the lemma for somethying
def degreesYFinset : Finset ℕ :=
  f.toFinsupp.support

lemma degreesYFinset_nonempty (hf : f ≠ 0) : (degreesYFinset f).Nonempty := by
  rw [degreesYFinset]
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)


def degreeY' (hf : f ≠ 0) : ℕ :=
  f.toFinsupp.support.max' (degreesYFinset_nonempty f hf)

/--
The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY : F[X] := f.coeff (natDegree f)

/--
The polynomial coeffient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial.
-/
theorem leadingCoeffY_eq_zero : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/--
The polynomial coeffient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero.
-/
lemma ne_zero_iff_leadingCoeffY_ne_zero : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero f]

/--
Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero.
-/
lemma ne_zero_mul_ne_zero [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := mul_ne_zero hf hg

/--
Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
lemma degreeY_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0)
  : degreeY (f * g) = degreeY f + degreeY g := by
  unfold degreeY
  rw [←ne_zero_iff_leadingCoeffY_ne_zero] at hf
  rw [←ne_zero_iff_leadingCoeffY_ne_zero] at hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

/--
The `X`-degree of a bivariate polynomial.
-/
def degreeX : ℕ := f.toFinsupp.support.sup (fun n => (f.coeff n).natDegree)

lemma natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
  (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intros f_x_deg others_le
  by_cases deg_zero : deg = 0
  · rw [←f_x_deg, Finset.sum_eq_single]
    · intros b h h'
      specialize others_le b h h'
      rw [deg_zero] at others_le
      simp only [not_lt_zero', false_or] at others_le
      exact others_le
    · intros h'
      exfalso
      apply h'
      exact h
  · have : ∑ x ∈ s, f x = (∑ x ∈ s.filter (fun x => x ≠ mx), f x) + f mx := by
      have : s.filter (fun x => x ≠ mx) ∪ {mx} = s := by
        apply Finset.ext
        intros a
        apply Iff.intro
        · aesop
        · simp only [ne_eq, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]; tauto
      rw (occs := .pos [1]) [this.symm]
      rw [Finset.sum_union (by simp), Finset.sum_singleton]
    rw [this, Polynomial.natDegree_add_eq_right_of_degree_lt]
    exact f_x_deg
    apply lt_of_le_of_lt
    exact Polynomial.degree_sum_le (s.filter (fun x => x ≠ mx)) f
    rw [Finset.sup_lt_iff]
    intros b h''
    simp only [ne_eq, Finset.mem_filter] at h''
    rcases others_le b h''.1 h''.2 with h' | h'
    · exact Polynomial.degree_lt_degree (f_x_deg.symm ▸ h')
    · rw [h', degree_zero]
      have : f mx ≠ 0 := by
        by_contra contra
        rw [contra] at f_x_deg
        simp only [natDegree_zero] at f_x_deg
        apply deg_zero
        exact f_x_deg.symm
      cases cs : (f mx).degree
      · rw [Polynomial.degree_eq_bot] at cs
        rw [cs] at f_x_deg
        simp only [natDegree_zero] at f_x_deg
        exfalso
        apply deg_zero
        exact f_x_deg.symm
      · simp
    have : f mx ≠ 0 := by aesop
    rw [Polynomial.degree_eq_natDegree this, f_x_deg]
    exact WithBot.bot_lt_coe _

lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
      (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  intros reach all_le
  haveI : Nonempty α := Nonempty.intro x
  rw [←reach] at all_le ⊢
  apply sup_eq_of_isMaxOn h
  rw [isMaxOn_iff]
  exact all_le

open Finset Finsupp Polynomial in
/--
The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
lemma degreeX_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  unfold degreeX
  let Pₙ (p : F[X][Y]) (n : ℕ) : ℕ := (p.coeff n).natDegree
  let Supₙ (p : F[X][Y]) := p.support.sup (Pₙ p)
  let SSetₙ (p : F[X][Y]) := {n ∈ p.support | Pₙ p n = Supₙ p}
  have nempty {p : F[X][Y]} (h : p ≠ 0) : (SSetₙ p).Nonempty := by
    unfold Finset.Nonempty
    convert exists_mem_eq_sup _ (support_nonempty.2 h) (Pₙ p)
    aesop
  let SSetₛ {p : F[X][Y]} (h : p ≠ 0) := SSetₙ p |>.max' (nempty h)
  change Supₙ (f * g) = Supₙ f + Supₙ g
  have pₙ_eq_Supₙ {p : F[X][Y]} (h : p ≠ 0) : Pₙ p (SSetₛ h) = Supₙ p := by
    have h := Finset.sup_mem_of_nonempty (s := SSetₙ p) (f := id) (nempty h)
    simp [SSetₙ, SSetₛ] at h ⊢
    convert h.2
    rw [Finset.max'_eq_sup', sup'_eq_sup]
  have supₙ_ne_zero {p : F[X][Y]} (h : p ≠ 0) : p.coeff (SSetₛ h) ≠ 0 := fun contra ↦ by
    have eq := Finset.sup_mem_of_nonempty (s := SSetₙ p) (f := id) (nempty h)
    simp [SSetₙ, SSetₛ, ←contra, Finset.max'_eq_sup', sup'_eq_sup] at eq
    tauto
  have h₁ {p : F[X][Y]} {n : ℕ} (h : p ≠ 0) : Pₙ p n ≤ Pₙ p (SSetₛ h) := by
    by_cases eq : n ∈ p.support
    · exact Finset.sup_le_iff.mp (le_of_eq (pₙ_eq_Supₙ h).symm) n eq
    · simp [Pₙ, Polynomial.notMem_support_iff.mp eq]
  have h₁' {p : F[X][Y]} {n : ℕ} (h : p ≠ 0) (hc : SSetₛ h < n) :
    Pₙ p n < Pₙ p (SSetₛ h) ∨ p.coeff n = 0 :=
    suffices p.coeff n ≠ 0 → Pₙ p n < Pₙ p (SSetₛ h) by tauto
    fun h₂ ↦ suffices Pₙ p n ≠ Pₙ p (SSetₛ h) by have := h₁ (n := n) h; omega
    fun h₃ ↦ by
    simp [SSetₛ, SSetₙ] at hc
    specialize hc _ h₂
    rw [h₃, pₙ_eq_Supₙ h] at hc
    omega
  conv_lhs =>
    unfold Supₙ
    rw [
      show Pₙ (f * g) =
           fun n ↦ (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree by
      funext n
      simp [Pₙ, Polynomial.coeff_mul]
    ]
  have : (∑ x ∈ Finset.antidiagonal (SSetₛ hf + SSetₛ hg), f.coeff x.1 * g.coeff x.2).natDegree =
          Supₙ f + Supₙ g := by
    apply natDeg_sum_eq_of_unique (SSetₛ hf, SSetₛ hg) (by simp)
    rw [
      Polynomial.natDegree_mul (supₙ_ne_zero hf) ((supₙ_ne_zero hg)), ←pₙ_eq_Supₙ hf, ←pₙ_eq_Supₙ hg
    ]
    rintro ⟨y₁, y₂⟩ h h'
    simp only [ne_eq, mem_antidiagonal, Prod.mk.injEq, not_and_or, mul_eq_zero, Pₙ] at *
    have : SSetₛ hf < y₁ ∨ SSetₛ hg < y₂ := by omega
    rw [←pₙ_eq_Supₙ hf, ←pₙ_eq_Supₙ hg]
    set P₁ := f.coeff y₁
    set P₂ := g.coeff y₂
    suffices P₁ ≠ 0 ∧ P₂ ≠ 0 → (P₁ * P₂).natDegree < Pₙ f (SSetₛ hf) + Pₙ g (SSetₛ hg) by tauto
    rintro ⟨hp₁, hp₂⟩
    apply lt_of_le_of_lt natDegree_mul_le
    rw [show P₁.natDegree = Pₙ f y₁ by aesop, show P₂.natDegree = Pₙ g y₂ by aesop]
    rcases this with this | this
    · have eq₁ : Pₙ f y₁ < Pₙ f (SSetₛ hf) := by have := h₁' hf this; tauto
      have eq₂ : Pₙ g y₂ ≤ Pₙ g (SSetₛ hg) := h₁ hg
      omega
    · have eq₁ : Pₙ g y₂ < Pₙ g (SSetₛ hg) := by have := h₁' hg this; tauto
      have eq₂ : Pₙ f y₁ ≤ Pₙ f (SSetₛ hf) := h₁ hf
      omega
  apply sup_eq_of_le_of_reach (SSetₛ hf + SSetₛ hg)
  · rw [Polynomial.mem_support_iff, Polynomial.coeff_mul]
    intros h
    rw [h, natDegree_zero] at this
    have : ∑ x ∈ Finset.antidiagonal (SSetₛ hf + SSetₛ hg), f.coeff x.1 * g.coeff x.2 =
           f.coeff (SSetₛ hf) * g.coeff (SSetₛ hg) := by
      apply Finset.sum_eq_single (f := fun x ↦ f.coeff x.1 * g.coeff x.2)
                                 (SSetₛ hf, SSetₛ hg)
                                 (h₁ := by simp)
      simp only [mem_antidiagonal, ne_eq, mul_eq_zero, Prod.forall, Prod.mk.injEq, not_and_or]
      rintro y₁ y₂ h' h''
      have : SSetₛ hf < y₁ ∨ SSetₛ hg < y₂ := by omega
      simp_rw [pₙ_eq_Supₙ] at h₁'
      rcases this with this | this
      · have := h₁' hf this
        simp [show Supₙ f = 0 by omega] at this
        tauto
      · have := h₁' hg this
        simp [show Supₙ g = 0 by omega] at this
        tauto
    aesop (add safe (by omega))
  · exact this
  · intros x h
    apply le_trans (natDegree_sum_le (Finset.antidiagonal x) (fun x ↦ f.coeff x.1 * g.coeff x.2))
    suffices ∀ (a b : ℕ), a + b = x → Pₙ f a + Pₙ g b ≤ Supₙ f + Supₙ g by
      simp [Finset.fold_max_le]
      exact fun a b h ↦ le_trans natDegree_mul_le (this a b h)
    simp_rw [pₙ_eq_Supₙ] at h₁
    intros a b _
    linarith [show _ from h₁ (n := a) hf, show _ from h₁ (n := b) hg]

/--
The evaluation at a point of a bivariate polynomial in the first variable `X`.
-/
def evalX : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`.
-/
def evalSetX (P : Finset F) [Nonempty P]: Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalX a f = h}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalY : Polynomial F := Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalSetY (P : Finset F) [Nonempty P] : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalY a f = h}

/--
The bivariate quotient polynomial.
-/
def quotient : Prop := ∃ q : F[X][Y], g = q * f

/--
The quotient of two non-zero bivariate polynomials is non-zero.
-/
lemma quotient_nezero (q : F[X][Y]) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by by_contra h; apply hg; simp [h_quot_XY, h]

/--
A bivariate polynomial is non-zero if and only if all its coefficients are non-zero.
-/
lemma nezero_iff_coeffs_nezero : f ≠ 0 ↔ f.coeff ≠ 0 := by
  apply Iff.intro
  · intro hf
    have f_finsupp : f.toFinsupp ≠ 0 := by aesop
    rw [coeff]
    simp only [ne_eq, Finsupp.coe_eq_zero]
    exact f_finsupp
  · intro f_coeffs
    rw [coeff] at f_coeffs
    aesop

/--
If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero.
-/
lemma quotient_nezero_iff_coeffs_nezero (q : F[X][Y]) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) : q.coeff ≠ 0 := by
  apply (nezero_iff_coeffs_nezero q).1
  exact quotient_nezero f g q hg h_quot_XY

/--
The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
lemma quotient_degX [IsDomain F](q : F[X][Y]) (h_quot_XY : g = q * f) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX q ≤ degreeX g - degreeX f := by
  rw [h_quot_XY, degreeX_mul q f]
  · aesop
  · rw [nezero_iff_coeffs_nezero]
    exact quotient_nezero_iff_coeffs_nezero f g q hg h_quot_XY
  · exact hf

/--
The `Y` degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
lemma quotient_degY [IsDomain F] (q : F[X][Y]) (h_quot_XY : g = q * f) (hf : f ≠ 0)
  (hg : g ≠ 0) : degreeY q  ≤ degreeY g - degreeY f := by
  rw [h_quot_XY, degreeY_mul q f]
  · aesop
  · rw [nezero_iff_coeffs_nezero q]
    exact quotient_nezero_iff_coeffs_nezero f g q hg h_quot_XY
  · exact hf

def monomial_y (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop


def monomial_xy (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, Polynomial.monomial_add, Polynomial.monomial_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw[smul_monomial, smul_monomial]
    simp

theorem monomial_xy_def (m n : ℕ) (c : F) : monomial_xy n m c = monomial m (monomial n c) := by
  unfold monomial_xy
  simp

theorem monomial_xy_add (n m : ℕ) (r s : F) :
  monomial_xy n m (r + s) = monomial_xy n m r + monomial_xy n m s :=
  (monomial_xy n m).map_add _ _

theorem monomial_xy_mul_monomial_xy (n m p q : ℕ) (r s : F) :
    monomial_xy n m r * monomial_xy p q s = monomial_xy (n + p) (m + q) (r * s) :=
  toFinsupp_injective <| by
  unfold monomial_xy
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]


@[simp]
theorem monomial_pow (n m k : ℕ) (r : F) :
  monomial_xy n m r ^ k = monomial_xy (n * k) (m * k) (r ^ k) := by
  unfold monomial_xy
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monomial_pow]


theorem smul_monomial_xy {S} [SMulZeroClass S F] (a : S) (n m : ℕ) (b : F) :
    a • monomial_xy n m b = monomial_xy n m (a • b) := by
    rw [monomial_xy]
    simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk]
    rw [@Polynomial.smul_monomial, @Polynomial.smul_monomial]


@[simp]
theorem monomial_xy_eq_zero_iff (t : F) (n m : ℕ) : monomial_xy n m t = 0 ↔ t = 0 := by
  rw [monomial_xy]
  simp

theorem monomial_xy_eq_monomial_xy_iff {m n p q : ℕ} {a b : F} :
    monomial_xy n m a = monomial_xy p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
    unfold monomial_xy
    simp
    rw [@monomial_eq_monomial_iff, @monomial_eq_monomial_iff]
    aesop

def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => m + (f.coeff m).natDegree)

lemma monomial_xy_degree (n m : ℕ) (a : F) (ha : a ≠ 0) :
  totalDegree (monomial_xy n m a) = n + m := by
  unfold totalDegree
  rw
    [
      monomial_xy_def,
      Polynomial.support_monomial,
      Finset.sup_singleton,
      Nat.add_comm
    ] <;> simp [ha]


theorem totalDegree_prod (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  unfold totalDegree
  rw [@mul_eq_sum_sum]
  sorry


end
end Bivariate
