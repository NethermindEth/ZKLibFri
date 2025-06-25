/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.ComputeDegree

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
  let Pₙ (p : F[X][Y]) (n : ℕ) : ℕ := (f.coeff n).natDegree
  let Supₙ (p : F[X][Y]) := p.support.sup (Pₙ p)
  let SSetₙ (p : F[X][Y]) := {n ∈ p.support | Pₙ p n = Supₙ p}
  have nempty {p : F[X][Y]} (h : p.support.Nonempty) : (SSetₙ p).Nonempty := by
    unfold Finset.Nonempty
    convert exists_mem_eq_sup _ h (Pₙ p)
    aesop
  let SSetₛ {p : F[X][Y]} (h : p ≠ 0) := SSetₙ p |>.max' (nempty (support_nonempty.2 h))
  -- generalize h_fdegx : s₁.sup (Pₙ f) = fdegx -- Supₙ f
  -- generalize h_gdegx : s₂.sup (Pₙ g) = gdegx -- Supₙ g
  -- have f_support_nonempty : s₁.Nonempty :=
  --   support_nonempty_iff.2 (by aesop (add safe forward toFinsupp_eq_zero))
  -- have g_support_nonempty : s₂.Nonempty :=
  --   support_nonempty_iff.2 (by aesop (add safe forward toFinsupp_eq_zero))
  have pₙ_eq_Supₙ {p : F[X][Y]} (h : p ≠ 0) : Pₙ p (SSetₛ h) = Supₙ p := by
    have h := Finset.sup_mem_of_nonempty (s := SSetₙ p) (f := id) (nempty (support_nonempty.2 h))
    simp [SSetₙ, SSetₛ] at h ⊢
    convert h.2
    rw [Finset.max'_eq_sup', sup'_eq_sup]
  have supₙ_ne_zero {p : F[X][Y]} (h : p ≠ 0) : p.coeff (SSetₛ h) ≠ 0 := fun contra ↦ by
    have eq := Finset.sup_mem_of_nonempty (s := SSetₙ p) (f := id) (nempty (support_nonempty.2 h))
    simp [SSetₙ, SSetₛ, ←contra, Finset.max'_eq_sup', sup'_eq_sup] at eq
    tauto
  have h₁ : ∀ n, (f.coeff n).natDegree ≤ (f.coeff mmfx).natDegree := by
    intros n
    by_cases h : n ∈ f.toFinsupp.support
    · have  : (f.toFinsupp.support.sup fun n ↦ (f.coeff n).natDegree) = (f.coeff mmfx).natDegree :=
        by aesop
      exact Finset.sup_le_iff.mp (le_of_eq this) n h
    · rw [Polynomial.notMem_support_iff.mp h]
      simp
  have h₂ : ∀ n, (g.coeff n).natDegree ≤ (g.coeff mmgx).natDegree := by
    intros n
    by_cases h : n ∈ g.toFinsupp.support
    · have : (g.toFinsupp.support.sup fun n ↦ (g.coeff n).natDegree) = (g.coeff mmgx).natDegree :=
        by aesop
      exact Finset.sup_le_iff.mp (le_of_eq this) n h
    · rw [Polynomial.notMem_support_iff.mp h]
      simp
  have h₁' : ∀ n, n > mmfx → (f.coeff n).natDegree < (f.coeff mmfx).natDegree ∨ f.coeff n = 0 := by
    intros n h
    by_cases h' : f.coeff n = 0
    · right; exact h'
    · left
      by_contra contra
      simp only [not_lt] at contra
      rcases Or.symm (Nat.eq_or_lt_of_le contra) with contra | contra
      · rw [mmfx_def] at contra
        have contra : fdegx < fdegx := by
          apply lt_of_lt_of_le
          exact contra
          rw [←h_fdegx]
          have := @Finset.le_sup ℕ ℕ _ _ f.toFinsupp.support (fun n ↦ (f.coeff n).natDegree)
          apply this
          rw [f.toFinsupp.mem_support_toFun]
          intros h''
          apply h'
          rw [←Polynomial.toFinsupp_apply]
          exact h''
        simp at contra
      · rw [mmfx_def] at contra
        have : n ≤ mmfx := by
          dsimp [mmfx]
          apply
            Finset.le_sup'_of_le
              (s := {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx})
              (b := n)
              id
          simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, contra.symm, and_true, mmfx]
          rw [Polynomial.toFinsupp_apply]
          exact h'
          rfl
        linarith
  have h₂' : ∀ n, n > mmgx → (g.coeff n).natDegree < (g.coeff mmgx).natDegree ∨ g.coeff n = 0 := by
    intros n h
    by_cases h' : g.coeff n = 0
    · right; exact h'
    · left
      by_contra contra
      simp only [not_lt] at contra
      rcases Or.symm (Nat.eq_or_lt_of_le contra) with contra | contra
      · rw [mmgx_def] at contra
        have contra : gdegx < gdegx := by
          apply lt_of_lt_of_le
          exact contra
          rw [←h_gdegx]
          have := @Finset.le_sup ℕ ℕ _ _ g.toFinsupp.support (fun n ↦ (g.coeff n).natDegree)
          apply this
          rw [g.toFinsupp.mem_support_toFun]
          intros h''
          apply h'
          rw [←Polynomial.toFinsupp_apply]
          exact h''
        simp at contra
      · rw [mmgx_def] at contra
        have : n ≤ mmgx := by
          dsimp [mmgx]
          apply
            Finset.le_sup'_of_le
              (s := {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx})
              (b := n)
              id
          simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, contra.symm, and_true, mmfx]
          rw [Polynomial.toFinsupp_apply]
          exact h'
          rfl
        linarith
  have : (fun n ↦ ((f * g).coeff n).natDegree) =
          (fun n ↦ (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree) := by
    funext n
    rw [Polynomial.coeff_mul]
  rw [this]
  have : (∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2).natDegree =
            fdegx + gdegx := by
    apply natDeg_sum_eq_of_unique (mmfx, mmgx) (by simp)
    simp only
    rw [Polynomial.natDegree_mul mmfx_neq_0 mmgx_neq_0, mmfx_def, mmgx_def]
    intros y h h'
    have : y.1 > mmfx ∨ y.2 > mmgx := by
      have h_anti : y.1 + y.2 = mmfx + mmgx := by aesop
      by_cases h : y.1 > mmfx
      · left; exact h
      · right
        simp only [gt_iff_lt, not_lt] at h
        rcases Or.symm (Nat.eq_or_lt_of_le h) with h'' | h''
        · linarith
        · rw [h''] at h_anti
          simp only [Nat.add_left_cancel_iff] at h_anti
          rw [←h'', ←h_anti] at h'
          simp at h'
    rcases this with h'' | h''
    · specialize h₁' y.1 h''
      rw [mmfx_def] at h₁'
      specialize h₂ y.2
      rw [mmgx_def] at h₂
      rcases h₁'
      · left
        apply lt_of_le_of_lt
        exact Polynomial.natDegree_mul_le
        linarith
      · right
        aesop
    · specialize h₂' y.2 h''
      rw [mmgx_def] at h₂'
      specialize h₁ y.1
      rw [mmfx_def] at h₁
      rcases h₂'
      · left
        apply lt_of_le_of_lt
        exact Polynomial.natDegree_mul_le
        linarith
      · right
        aesop
  apply sup_eq_of_le_of_reach (mmfx + mmgx)
  · rw [Finsupp.mem_support_iff, Polynomial.toFinsupp_apply, Polynomial.coeff_mul]
    by_contra h
    rw [h, natDegree_zero] at this
    have fdegx_eq_0 : fdegx = 0 := by
      have := this.symm
      rw [Nat.add_eq_zero] at this
      exact this.1
    have gdegx_eq_0 : gdegx = 0 := by
      have := this.symm
      rw [Nat.add_eq_zero] at this
      exact this.2
    have : ∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2 =
              f.coeff mmfx * g.coeff mmgx := by
      have := @Finset.sum_eq_single (ℕ × ℕ) F[X] _ (Finset.antidiagonal (mmfx + mmgx))
                (fun x ↦ f.coeff x.1 * g.coeff x.2) (mmfx, mmgx)
      apply this
      · intros b h' h''
        have : b.1 > mmfx ∨ b.2 > mmgx := by
          simp only [Finset.mem_antidiagonal] at h'
          by_cases cond : b.1 > mmfx
          · left; exact cond
          · right
            simp only [gt_iff_lt, not_lt] at cond
            rcases Or.symm (Nat.eq_or_lt_of_le cond) with h'' | h'''
            · linarith
            · rw [h'''] at h'
              simp only [Nat.add_left_cancel_iff] at h'
              rw [←h''', ←h'] at h''
              simp at h''
        rcases this with h' | h'
        · specialize h₁' b.1 h'
          rw [mmfx_def, fdegx_eq_0] at h₁'
          simp only [not_lt_zero', false_or] at h₁'
          simp [h₁']
        · specialize h₂' b.2 h'
          rw [mmgx_def, gdegx_eq_0] at h₂'
          simp only [not_lt_zero', false_or] at h₂'
          simp [h₂']
      · simp
    rw [this] at h
    have h := h.symm
    rw [zero_eq_mul] at h
    rcases h with h | h
    · apply mmfx_neq_0
      exact h
    · apply mmgx_neq_0
      exact h
  · exact this
  · intros x h
    transitivity
    exact Polynomial.natDegree_sum_le (Finset.antidiagonal x) (fun x ↦ f.coeff x.1 * g.coeff x.2)
    rw [Finset.fold_max_le]
    simp only [zero_le, Finset.mem_antidiagonal, Function.comp_apply, Prod.forall, true_and]
    intros a b h'
    transitivity
    exact Polynomial.natDegree_mul_le
    specialize h₁ a
    rw [mmfx_def] at h₁
    specialize h₂ b
    rw [mmgx_def] at h₂
    linarith

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
