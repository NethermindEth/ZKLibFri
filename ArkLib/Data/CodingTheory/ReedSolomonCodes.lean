import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes
import Mathlib.Data.Matrix.Defs
import ArkLib.Data.CodingTheory.Prelims

open Classical
open Polynomial

variable {ι : ℕ}
         {F : Type*}
         {C : Set (Fin ι → F)}

noncomputable section

namespace Vandermonde

/--
A non-square Vandermonde matrix.
-/
def nonsquare [Semiring F] (deg : ℕ) (α : Fin ι ↪ F) : Matrix (Fin ι) (Fin deg) F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F]
                          {deg : ℕ} {α₁ : Fin ι ↪ F} {α₂ : Fin deg → F} {i : Fin ι} :
  (nonsquare deg α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ (↑x : ℕ) := by
  simp [nonsquare, Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]

/--
The transpose of a non-square Vandermonde matrix.
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare deg α).transpose

/--
The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subUpFull_of_vandermonde_is_vandermonde [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} (h : deg ≤ ι)
  :
  Matrix.vandermonde (Embedding.restrictionToFun deg α h) =
  Matrix.subUpFull (nonsquare deg α) h := by
  unfold Matrix.subUpFull nonsquare Matrix.vandermonde
  aesop

/--
The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subLeftFull_of_vandermonde_is_vandermonde [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} (h : ι ≤ deg)
  : Matrix.vandermonde α = Matrix.subLeftFull (nonsquare deg α) h := by
  unfold Matrix.subLeftFull nonsquare Matrix.vandermonde
  aesop

/--
The rank of a non-square Vandermonde matrix with more rows than columns is the number of columns.
-/
lemma rank_nonsquare_eq_deg_of_deg_le [CommRing F] [IsDomain F] {deg : ℕ} {α : Fin ι ↪ F}
  (h : deg ≤ ι) :
  (Vandermonde.nonsquare deg α).rank = deg := by
    rw [
      Matrix.full_col_rank_via_rank_subUpFull (h_col := h),
      ← subUpFull_of_vandermonde_is_vandermonde,
      Matrix.full_rank_iff_det_ne_zero,
      Matrix.det_vandermonde_ne_zero_iff
    ]
    apply Embedding.restrictionToFun_injective

/--
The rank of a non-square Vandermonde matrix with more columns than rows is the number of rows.
-/
lemma rank_nonsquare_eq_deg_of_ι_le [CommRing F] [IsDomain F] {deg : ℕ} {α : Fin ι ↪ F}
  (h : ι ≤ deg) :
  (Vandermonde.nonsquare deg α).rank = ι := by
  rw [
    Matrix.full_row_rank_via_rank_subLeftFull (h_row := h),
    ← subLeftFull_of_vandermonde_is_vandermonde,
    Matrix.full_rank_iff_det_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff
  ]
  exact α.injective

@[simp]
lemma rank_nonsquare_rows_eq_min [CommRing F] [IsDomain F] {deg : ℕ} {α : Fin ι ↪ F} :
  (Vandermonde.nonsquare deg α).rank = min ι deg := by
  by_cases h : ι ≤ deg <;>
  aesop (add simp [rank_nonsquare_eq_deg_of_ι_le, rank_nonsquare_eq_deg_of_deg_le])
        (add safe forward le_of_lt)  

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
  {deg : ℕ} [CommRing F] {v : Fin ι ↪ F}
  {p : F[X]} (h_deg : p.natDegree ≤ deg) :
    (Vandermonde.nonsquare (deg + 1) v).mulVecLin (p.coeff ∘ Fin.val) =
    fun i => p.eval (v i) := by
  ext i
  simp only [
    nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, eval_eq_sum
  ]
  refine Eq.symm (Finset.sum_of_injOn (·%(deg + 1)) ?p₁ ?p₂ (fun i _ h ↦ ?p₃) (fun i _ ↦ ?p₄))
  · aesop (add simp [Set.InjOn])
          (add safe forward [Polynomial.le_natDegree_of_mem_supp, le_trans, Nat.lt_add_one_of_le])
          (add 10% apply (show ∀ {a b c : ℕ}, a < c → b < c → a % c = b % c → a = b from
                                 fun h₁ h₂ ↦ by aesop (add simp Nat.mod_eq_of_lt)))
          (erase simp mem_support_iff)
  · aesop (add simp Set.MapsTo) (add safe apply Nat.mod_lt)
  · aesop (add safe (by specialize h i)) (add simp Nat.mod_eq_of_lt)
  · have : i < deg + 1 := by aesop (add safe forward Polynomial.le_natDegree_of_mem_supp)
                                   (erase simp mem_support_iff)
                                   (add safe (by omega))
    aesop (add simp Nat.mod_eq_of_lt) (add safe (by ring))

end Vandermonde

namespace ReedSolomonCode

lemma natDegree_lt_of_lbounded_zero_coeff [Semiring F] {p : F[X]} {deg : ℕ} [NeZero deg]
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

def polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi a))
                     (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
  ⟩

lemma natDegree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

lemma coeff_polynomialOfCoeffs_eq_coeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff ∘ Fin.val = coeffs:= by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffs)

-- lemma exists_poly_of_coeffs [Semiring F] (deg : ℕ) [NeZero deg] (coeffs : Fin deg → F) :
--   ∃ p : F[X], coeffs = p.coeff ∘ Fin.val ∧ p.natDegree < deg := by
--   let p : F[X] :=
--     ⟨
--       Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
--       fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0, -- NOTE TO SELF: Use `liftF` I implemented
--                                                         -- in some of the BW cleanups?
--       by
--         dsimp
--         intros a
--         simp_all only
--           [
--             Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
--             true_and, Function.Embedding.coeFn_mk,
--             dite_eq_right_iff, not_forall
--           ]
--         apply Iff.intro
--         · intro a_1
--           obtain ⟨w, h⟩ := a_1
--           obtain ⟨left, right⟩ := h
--           subst right
--           simp_all only [Fin.eta, not_false_eq_true, Fin.is_lt, exists_const,]
--         · intro a_1
--           obtain ⟨w, h⟩ := a_1
--           exists ⟨a, w⟩
--     ⟩
--   exists p
--   simp only [coeff_ofFinsupp, Finsupp.coe_mk, support, p]
--   apply And.intro
--   · aesop
--   · apply natDegree_lt_of_lbounded_zero_coeff; aesop

/--
The generator matrix of a Reed-Solomon code is a Vandermonde matrix.
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
    let p := polynomialOfCoeffs coeffs
    have p_deg : p.natDegree < deg := natDegree_polynomialOfCoeffs_deg_lt_deg
    have h' : p.coeff ∘ Fin.val = coeffs := coeff_polynomialOfCoeffs_eq_coeffs
    -- rcases exists_poly_of_coeffs deg coeffs with ⟨p, h', p_deg⟩
    rw [←h'] at h
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
      rw [Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials, ←h.2]
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

-- for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
-- Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly. Worth mentioning??

/--
The dimension of a Reed-Solomon code is the maximal degree of the polynomials.
-/
lemma dim_eq_deg [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw [←genMatIsVandermonde, ←LinearCodes.dimEqRankGenMat]
  aesop

/--
The length of a Reed-Solomon code is the domain size.
-/
lemma length_eq_domain_size [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.length (ReedSolomon.code α deg) = ι := by
  rw[LinearCodes.length]
  simp

/--
The rate of a Reed-Solomon code.
-/
lemma rate [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / ι := by
  rw[LinearCodes.rate, dim_eq_deg, length_eq_domain_size]
  exact h

/--
The minimal code distance of a Reed-Solomon given by the degree and domain size.
-/
lemma minDist [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by sorry



end ReedSolomonCode
end
