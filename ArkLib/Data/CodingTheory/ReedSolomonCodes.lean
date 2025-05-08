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
  {deg : ℕ} [NeZero deg] [CommRing F] {v : Fin ι ↪ F}
  {p : F[X]} (h_deg : p.natDegree < deg) :
    (Vandermonde.nonsquare deg v).mulVecLin (p.coeff ∘ Fin.val) = -- NOTE: Use `liftF`.
    fun i => p.eval (v i) := by
  ext i
  simp only [
    nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, eval_eq_sum
  ]
  refine Eq.symm (Finset.sum_of_injOn (·%deg) ?p₁ ?p₂ (fun i _ h ↦ ?p₃) (fun i _ ↦ ?p₄))
  · aesop (add simp [Set.InjOn])
          (add safe forward [le_natDegree_of_mem_supp, lt_of_le_of_lt, Nat.lt_add_one_of_le])
          (add 10% apply (show ∀ {a b c : ℕ}, a < c → b < c → a % c = b % c → a = b from
                                 fun h₁ h₂ ↦ by aesop (add simp Nat.mod_eq_of_lt)))
          (erase simp mem_support_iff)
  · aesop (add simp Set.MapsTo) (add safe apply Nat.mod_lt) (add 1% cases Nat)
  · aesop (add safe (by specialize h i)) (add simp Nat.mod_eq_of_lt)
  · have : i < deg := by aesop (add safe forward le_natDegree_of_mem_supp)
                               (erase simp mem_support_iff)
                               (add safe (by omega))
    aesop (add simp Nat.mod_eq_of_lt) (add safe (by ring))

end Vandermonde

namespace ReedSolomonCode

section

variable [Semiring F] {p : F[X]}
         {deg : ℕ} [NeZero deg]
         {coeffs : Fin deg → F}

lemma natDegree_lt_of_lbounded_zero_coeff 
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

def polynomialOfCoeffs (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi a))
                     (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
  ⟩

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg : (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg : (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs :
  (polynomialOfCoeffs coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT : polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

lemma natDegree_lt_of_mem_degreeLT (h : p ∈ degreeLT F deg) : p.natDegree < deg := by
  by_cases p = 0
  · cases deg <;> aesop
  · aesop (add simp [natDegree_lt_iff_degree_lt, mem_degreeLT])

end

section

variable {deg : ℕ} [Field F] {α : Fin ι ↪ F}

/--
The generator matrix of a Reed-Solomon code is a Vandermonde matrix.
-/
lemma genMatIsVandermonde [NeZero deg] :
  LinearCodes.genMat_mul (Vandermonde.nonsquare deg α) = ReedSolomon.code α deg := by
  unfold LinearCodes.genMat_mul ReedSolomon.code
  ext x; rw [LinearMap.mem_range, Submodule.mem_map]
  refine ⟨
    fun ⟨coeffs, h⟩ ↦ ⟨polynomialOfCoeffs coeffs, h.symm ▸ ?p₁⟩,
    fun ⟨p, h⟩ ↦ ⟨p.coeff ∘ Fin.val, ?p₂⟩
  ⟩
  · rw [
      ←coeff_polynomialOfCoeffs_eq_coeffs (coeffs := coeffs),
      Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials (by simp)
    ]
    simp [ReedSolomon.evalOnPoints]
  · exact h.2 ▸ Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
                  (natDegree_lt_of_mem_degreeLT h.1)

-- for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
-- Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly. Worth mentioning??

lemma dim_eq_deg [NeZero deg] (h : deg ≤ ι) :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw [←genMatIsVandermonde, ←LinearCodes.dimEqRankGenMat]
  aesop

@[simp]
lemma length_eq_domain_size :
  LinearCodes.length (ReedSolomon.code α deg) = ι := by
  rw [LinearCodes.length]
  simp

lemma rate [NeZero deg] (h : deg ≤ ι) :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / ι := by
  rwa [LinearCodes.rate, dim_eq_deg, length_eq_domain_size]

/--
The minimal code distance of a Reed-Solomon given by the degree and domain size.
-/
lemma minDist [NeZero deg] (h : deg ≤ ι) :
  LinearCodes.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by
  have : NeZero ι := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ => sorry
  case p₂ =>
    choose c hc using show ∃ c, c ∈ ReedSolomon.code α deg by sorry
    let p := polynomialOfCoeffs c
    sorry

end

end ReedSolomonCode
end
