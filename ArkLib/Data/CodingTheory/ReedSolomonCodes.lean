import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes

open Classical
open Polynomial

variable {ι : ℕ}
         {F : Type*}
         {C : Set (Fin ι → F)}

--abbrev LinearCode.{u} (F : Type u) [Semiring F] : Type u := Submodule F ((Fin ι) → F)

noncomputable section

namespace Vandermonde
/--
  `ι x deg` Vandermonde matrix
-/
def nonsquare [Semiring F] (deg : ℕ) (α : Fin ι ↪ F) : Matrix (Fin ι) (Fin deg) F :=
  Matrix.of (fun i j => (α i) ^ j.1)

/--
  The transpose of a `ι x deg` Vandermonde matrix
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare deg α).transpose

  #check Matrix.vandermonde

-- also requires α_i being distinct but we already have this with the embedding Fin ι ↪ F
-- and is generally true for RS codes.
-- TBD: keep α implicit or explicit

lemma nonsquareRank [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} :
  (Vandermonde.nonsquare deg α).rank = min deg ι := by sorry

lemma upper_corner_matrix_of_Van_is_Van [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} (h : deg ≤ ι) :
sorry := by sorry

theorem eval_matrixOfPolynomials_eq_nsvandermonde_mul_matrixOfPolynomials
  {deg : ℕ} [CommRing F] {v : Fin ι ↪ F}
  {p : F[X]} (h_deg : p.natDegree ≤ deg) :
    (Vandermonde.nonsquare (deg + 1) v).mulVecLin (p.coeff ∘ Fin.val) =
    (fun i => (p.eval (v i))) := by
  rw [Matrix.mulVecLin_apply]
  unfold Matrix.mulVec Vandermonde.nonsquare dotProduct
  simp only [Matrix.of_apply, Function.comp_apply]
  funext i
  rw [Polynomial.eval_eq_sum, sum_def]
  apply Eq.symm
  apply Finset.sum_of_injOn (Fin.ofNat' (deg + 1))
  · unfold Set.InjOn
    intro x₁ h₁ x₂ h₂ h
    have h₁' : x₁ < deg + 1 := by
      have := Polynomial.le_natDegree_of_mem_supp _ h₁
      linarith
    have h₂' : x₂ < deg + 1 := by
      have := Polynomial.le_natDegree_of_mem_supp _ h₂
      linarith
    have : (Fin.ofNat' (deg + 1) x₁ : ℕ) = (Fin.ofNat' (deg + 1) x₁ : ℕ) := by rfl
    rw (occs := .pos [2]) [h] at this
    rw [Fin.val_ofNat', Fin.val_ofNat', Nat.mod_eq_of_lt h₁', Nat.mod_eq_of_lt h₂'] at this
    exact this
  · unfold Set.MapsTo
    intros x h
    simp
  · intros i _ h
    simp only [Fin.ofNat'_eq_cast, Set.mem_image, Finset.mem_coe, mem_support_iff, ne_eq,
      not_exists, not_and] at h
    specialize h i.val
    simp only [Fin.cast_val_eq_self, not_true_eq_false, imp_false, Decidable.not_not] at h
    rw [h, mul_zero]
  · intros i h
    rw [Fin.val_ofNat']
    have : i < deg + 1 := by
      apply lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp i h)
      linarith
    rw [Nat.mod_eq_of_lt this]
    ring

end Vandermonde

namespace ReedSolomonCode

lemma degree_lt [Semiring F] {p : F[X]} {deg : ℕ} [NeZero deg] :
    (∀ i, i ≥ deg → p.coeff i = 0) → p.natDegree < deg := by
  intro h
  by_contra! h'
  specialize h p.natDegree h'
  simp_all only
    [
      coeff_natDegree, leadingCoeff_eq_zero, natDegree_zero,
      nonpos_iff_eq_zero, neZero_zero_iff_false
    ]

lemma exists_poly_of_coeffs [Semiring F] (deg : ℕ) [NeZero deg] (coeffs : Fin deg → F) :
    ∃ p : F[X], coeffs = p.coeff ∘ Fin.val ∧ p.natDegree < deg := by
  have : Function.Injective (Fin.val : Fin deg → ℕ) := by
    unfold Function.Injective
    aesop
  let support := Finset.map ⟨Fin.val, this⟩ (Finset.filter (fun i ↦ coeffs i ≠ 0) Finset.univ)
  let p : F[X] :=
    ⟨
      support,
      fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
      by
        dsimp [support]
        intros a
        simp_all only
          [
            Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
            true_and, Function.Embedding.coeFn_mk,
            dite_eq_right_iff, not_forall, support
          ]
        apply Iff.intro
        · intro a_1
          obtain ⟨w, h⟩ := a_1
          obtain ⟨left, right⟩ := h
          subst right
          simp_all only [Fin.eta, not_false_eq_true, Fin.is_lt, exists_const, support]
        · intro a_1
          obtain ⟨w, h⟩ := a_1
          exists ⟨a, w⟩
    ⟩
  exists p
  simp only [coeff_ofFinsupp, Finsupp.coe_mk, support, p]
  apply And.intro
  · aesop
  · apply degree_lt; aesop

/--
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Field F] {deg : ℕ} [inst : NeZero deg] (α : Fin ι ↪ F) :
  LinearCodes.genMat_mul (Vandermonde.nonsquare deg α) = ReedSolomon.code α deg := by
  unfold LinearCodes.genMat_mul ReedSolomon.code
  apply Submodule.ext
  intros x
  apply Iff.intro
  · intros h
    rw [LinearMap.mem_range] at h
    rcases h with ⟨coeffs, h⟩
    rcases exists_poly_of_coeffs deg coeffs with ⟨p, h', p_deg⟩
    rw [h'] at h
    match deg_def : deg with
    | .zero => aesop
    | deg + 1 =>
      rw [Vandermonde.eval_matrixOfPolynomials_eq_nsvandermonde_mul_matrixOfPolynomials (by linarith)] at h
      rw [←h, Submodule.mem_map]
      exists p
      apply And.intro
      · rw [Polynomial.mem_degreeLT]
        by_cases p_ne_zero : p ≠ 0
        · rw
            [
              Polynomial.degree_eq_natDegree p_ne_zero,
              Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe
            ]
          exact p_deg
        · simp only [ne_eq, Decidable.not_not] at p_ne_zero
          rw [p_ne_zero, Polynomial.degree_zero, Nat.cast_withBot]
          simp
          decide
      · simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
  · intros h
    rw [Submodule.mem_map] at h
    rcases h with ⟨p, h⟩
    rw [LinearMap.mem_range]
    exists (p.coeff ∘ Fin.val)
    match def_def : deg with
    | .zero => aesop
    | deg + 1 =>
      rw [Polynomial.mem_degreeLT] at h
      rw [Vandermonde.eval_matrixOfPolynomials_eq_nsvandermonde_mul_matrixOfPolynomials, ←h.2]
      unfold ReedSolomon.evalOnPoints
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      by_cases p_ne_zero : p ≠ 0
      · rw
          [
            Polynomial.degree_eq_natDegree p_ne_zero,
            Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe
          ] at h
        linarith
      · aesop

-- our lemma Vandermonde.nonsquareRank will finish the proof because we fall into the first case.
-- for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
-- Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly.

lemma dim_eq_deg [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw [← genMatIsVandermonde, ← LinearCodes.dimEqRankGenMat, Vandermonde.nonsquareRank]
  simp [h]

lemma length_eq_domain_size [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.length (ReedSolomon.code α deg) = ι := by
  rw[LinearCodes.length]
  simp

lemma rate [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / ι := by
  rw[LinearCodes.rate, dim_eq_deg, length_eq_domain_size]
  exact h

/--
  The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`
-/
lemma minDist [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by sorry



end ReedSolomonCode
end
