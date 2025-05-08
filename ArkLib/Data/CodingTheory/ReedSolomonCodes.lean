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
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F]
                          {deg : ℕ} {α₁ : Fin ι ↪ F} {α₂ : Fin deg → F} {i : Fin ι} :
  (nonsquare deg α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ (↑x : ℕ) := by
  simp [nonsquare, Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]

/--
  The transpose of a `ι x deg` Vandermonde matrix
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare deg α).transpose

-- also requires α_i being distinct but we already have this with the embedding Fin ι ↪ F
-- and is generally true for RS codes.
-- TBD: keep α implicit or explicit

lemma nonsquareRank [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} :
  (Vandermonde.nonsquare deg α).rank = min deg ι := by sorry

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
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
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

-- our lemma Vandermonde.nonsquareRank will finish the proof because we fall into the first case.
-- for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
-- Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly.

lemma dim_eq_deg [NeZero deg] (h : deg ≤ ι) :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw [← genMatIsVandermonde, ← LinearCodes.dimEqRankGenMat, Vandermonde.nonsquareRank]
  simp [h]

@[simp]
lemma length_eq_domain_size :
  LinearCodes.length (ReedSolomon.code α deg) = ι := by
  rw [LinearCodes.length]
  simp

lemma rate [NeZero deg] (h : deg ≤ ι) :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / ι := by
  rwa [LinearCodes.rate, dim_eq_deg, length_eq_domain_size]

/--
  The minimal code distance of an RS code of length `ι` and dimensio `deg` is `ι - deg + 1`
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
