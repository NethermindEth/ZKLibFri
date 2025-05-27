import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes
import Mathlib.Data.Matrix.Defs
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib

open Classical
open Polynomial

variable {F ι : Type*}
         {C : Set (ι → F)}

noncomputable section

namespace Vandermonde

/--
A non-square Vandermonde matrix.
-/
def nonsquare [Semiring F] (deg : ℕ) (α : ι ↪ F) : Matrix ι (Fin deg) F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F]
                          {deg : ℕ} {α₁ : ι ↪ F} {α₂ : Fin deg → F} {i : ι} :
  (nonsquare deg α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ x.1 := by
  simp [nonsquare, Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]

/--
The transpose of a non-square Vandermonde matrix.
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : ι ↪ F) : Matrix (Fin deg) ι F :=
  (Vandermonde.nonsquare deg α).transpose

/--
The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subUpFull_of_vandermonde_is_vandermonde [FinEnum ι] [CommRing F] {deg : ℕ} {α : ι ↪ F}
  (h : deg ≤ FinEnum.card ι) :
  Matrix.vandermonde (FinEnum.fnOfFinFun deg h α) =
  Matrix.subUpFull (nonsquare deg α) h := by
  unfold Matrix.subUpFull nonsquare Matrix.vandermonde
  aesop

/--
The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subLeftFull_of_vandermonde_is_vandermonde [CommRing F] {deg ι : ℕ} {α : Fin ι ↪ F}
  (h : ι ≤ deg) : Matrix.vandermonde α = Matrix.subLeftFull (nonsquare deg α) h := by
  unfold Matrix.subLeftFull nonsquare Matrix.vandermonde
  aesop

/--
The rank of a non-square Vandermonde matrix with more rows than columns is the number of columns.
-/
lemma rank_nonsquare_eq_deg_of_deg_le [Fintype ι] [CommRing F] [IsDomain F] {deg : ℕ} {α : ι ↪ F}
  (h : deg ≤ Fintype.card ι) :
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
lemma rank_nonsquare_eq_deg_of_ι_le {ι : ℕ} [CommRing F] [IsDomain F] {deg : ℕ} {α : Fin ι ↪ F}
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
lemma rank_nonsquare_rows_eq_min [FinEnum ι] [CommRing F] [IsDomain F] {deg : ℕ} {α : ι ↪ F} :
  (Vandermonde.nonsquare deg α).rank = min (Fintype.card ι) deg := by
  by_cases h : Fintype.card ι ≤ deg <;>
  aesop (add simp [rank_nonsquare_eq_deg_of_ι_le, rank_nonsquare_eq_deg_of_deg_le])
        (add safe forward le_of_lt)  

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
  {deg : ℕ} [NeZero deg] [CommRing F] {v : ι ↪ F} {p : F[X]}
  (h_deg : p.natDegree < deg) :
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

def coeffsOfPolynomial [Semiring F] {deg : ℕ} [NeZero deg] (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffs)

lemma coeff_polynomialOfCoeffs_eq_coeffs'
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

@[simp]
lemma polynomialOfCoeffs_eq_zero [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffs, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffs_coeffsOfPolynomial [Semiring F] {deg : ℕ} [NeZero deg] {p : F[X]}
  (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))

@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg]
  {coeffs : Fin deg → F} : coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

@[simp]
lemma eval_polynomialsOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {α : F} :
  (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, coeff_polynomialOfCoeffs_eq_coeffs']

@[simp]
lemma isRoot_polynomialsOfCoeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {x : F} :
  IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl

lemma natDegree_lt_of_mem_degreeLT
  [Semiring F] {deg : ℕ} [NeZero deg] {p : F[X]} (h : p ∈ degreeLT F deg) : p.natDegree < deg := by
  by_cases p = 0
  · cases deg <;> aesop
  · aesop (add simp [natDegree_lt_iff_degree_lt, mem_degreeLT])

def encode [Semiring F] {deg ι : ℕ} [NeZero deg] [NeZero ι]
  (msg : Fin deg → F) (domain : Fin ι ↪ F) : Fin ι → F := (polynomialOfCoeffs msg).eval ∘ ⇑domain

lemma encode_mem_ReedSolomon_code
  [Semiring F] {deg ι : ℕ} [NeZero deg] [NeZero ι] {msg : Fin deg → F} {domain : Fin ι ↪ F} :
  encode msg domain ∈ ReedSolomon.code domain deg :=
  ⟨polynomialOfCoeffs msg, ⟨by simp, by ext i; simp [encode, ReedSolomon.evalOnPoints]⟩⟩

def makeZero (ι : ℕ) (F : Type*) [Zero F] : Fin ι → F := fun _ ↦ 0

@[simp]
lemma codewordIsZero_makeZero {ι : ℕ} {F : Type*} [Zero F] :
  makeZero ι F = 0 := by unfold makeZero; ext; rfl

/--
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Field F] {deg : ℕ} [inst : NeZero deg] (α : ι ↪ F) :
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

/- Our lemma Vandermonde.nonsquareRank will finish the proof because we fall into the first case.
for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly.-/

lemma dim_eq_deg_of_le [Fintype ι] [Field F] {deg : ℕ} [NeZero deg] {α : ι ↪ F} (h : deg ≤ Fintype.card ι) :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw [← genMatIsVandermonde, ← LinearCodes.dimEqRankGenMat, Vandermonde.rank_nonsquare_rows_eq_min]
  simp [h]

@[simp]
lemma length_eq_domain_size [Fintype ι] [Field F] {deg : ℕ} {α : ι ↪ F} :
  LinearCodes.length (ReedSolomon.code α deg) = Fintype.card ι := rfl

lemma rate [Field F] [Fintype ι] {deg : ℕ} [NeZero deg] {α : ι ↪ F} (h : deg ≤ Fintype.card ι) :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / Fintype.card ι := by
  rw [LinearCodes.rate, dim_eq_deg_of_le, length_eq_domain_size]
  exact h

@[simp]
lemma dist_le_length [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} :
    LinearCode.minDist (ReedSolomon.code α deg) ≤ ι := by
  convert LinearCode.minDist_UB

lemma card_le_card_of_count_inj {α β : Type*} {s : Multiset α} {s' : Multiset β}
  (f : α → β) (inj : Function.Injective f)
  (h : ∀ a : α, s.count a ≤ s'.count (f a)) : s.card ≤ s'.card := by
  simp only [←Multiset.toFinset_sum_count_eq]
  apply le_trans (b := ∑ x ∈ s.toFinset, s'.count (f x)) (Finset.sum_le_sum (by aesop))
  rw [←Finset.sum_image (f := s'.count) (by aesop)]
  have : s.toFinset.image f ⊆ s'.toFinset :=
    suffices ∀ x ∈ s, f x ∈ s' by simpa [Finset.image_subset_iff]
    by simp_rw [←Multiset.count_pos]
       exact fun x h' ↦ lt_of_lt_of_le h' (h x)
  exact Finset.sum_le_sum_of_subset_of_nonneg this (by aesop)

/--
  This should go elsewhere, of course.

  Is this named appropriately?
-/
def ReedSolomon.constantCode {α : Type*} (x : α) (deg : ℕ) : Fin deg → α := fun _ ↦ x

@[simp]
lemma ReedSolomon.weight_constantCode [Semiring F] {deg : ℕ} {x : F} :
  wt (ReedSolomon.constantCode x deg) = 0 ↔ deg = 0 ∨ x = 0 := by
  rw [wt_eq_zero_iff]; rcases deg <;> simp [constantCode]

@[simp]
lemma ReedSolomon.constantCode_mem_code
  [Semiring F] {α : Fin ι ↪ F} {x : F} {deg : ℕ} [NeZero deg] :
  ReedSolomon.constantCode x ι ∈ ReedSolomon.code α deg := by
  use C x
  aesop (add simp [ReedSolomon.evalOnPoints, coeff_C, degreeLT])

@[simp]
lemma ReedSolomon.constantCode_eq_ofNat_zero_iff [Semiring F] {x : F} [NeZero ι] :
  ReedSolomon.constantCode x ι = 0 ↔ x = 0 := by
  unfold constantCode
  exact ⟨fun x ↦ Eq.mp (by simp) (congrFun x), (· ▸ rfl)⟩

@[simp]
lemma ReedSolomon.wt_constantCode [Semiring F] {x : F} [NeZero x] :
  wt (ReedSolomon.constantCode x ι) = ι := by unfold constantCode wt; aesop

open Finset in
/--
  The minimal code distance of an RS code of length `ι` and dimensio `deg` is `ι - deg + 1`
-/
theorem minDist [Field F] [Inhabited F] {deg ι : ℕ} {α : Fin ι ↪ F} [φ : NeZero deg] (h : deg ≤ ι) :
  LinearCode.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by
  have : NeZero ι := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ =>
    have distUB := LinearCode.singletonBound (LC := ReedSolomon.code α deg)
    rw [dim_eq_deg_of_le h] at distUB
    zify [dist_le_length] at distUB
    omega
  case p₂ =>
    rw [LinearCode.minDist_eq_minWtCodewords]
    apply le_csInf (by use ι, ReedSolomon.constantCode 1 ι; simp)
    intro b ⟨msg, ⟨p, p_deg, p_eval_on_α_eq_msg⟩, msg_neq_0, wt_c_eq_b⟩
    let zeroes : Finset _ := {i | msg i = 0}
    have eq₁ : zeroes.val.Nodup := by
      aesop (add simp [Multiset.nodup_iff_count_eq_one, Multiset.count_filter])
    have msg_zeros_lt_deg : #zeroes < deg := by
      apply lt_of_le_of_lt (b := p.roots.card)
                            (hbc := lt_of_le_of_lt (Polynomial.card_roots' _)
                                                   (natDegree_lt_of_mem_degreeLT p_deg))
      exact card_le_card_of_count_inj α α.injective fun i ↦
        if h : msg i = 0
        then suffices 0 < Multiset.count (α i) p.roots by
                rwa [@Multiset.count_eq_one_of_mem (d := eq₁) (h := by simpa [zeroes])]
              by aesop
        else by simp [zeroes, h]
    have : #zeroes + wt msg = ι := by
      simp_rw [show ι = #(univ : Finset (Fin ι)) by simp]
      rw [wt, filter_card_add_filter_neg_card_eq_card]
    omega

end ReedSolomonCode
end
