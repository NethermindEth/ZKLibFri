import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

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

lemma natDegree_lt_of_lbounded_zero_coeff [Semiring F] {p : F[X]} {deg : ℕ} [NeZero deg]
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

def polynomialOfCoeffs [Semiring F] {deg : ℕ} (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    by
      intros a
      apply Iff.intro
      · intros h
        simp at h
        rcases h with ⟨a_fin, h⟩
        simp
        rw [←h.2]
        exists a_fin.2
        exact h.1
      · simp
        intros h h'
        exists ⟨a, h⟩


    --  aesop (add safe (by existsi a))
    --                  (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
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
  encode msg domain ∈ ReedSolomon.code domain deg := by
  simp [encode, ReedSolomon.code]
  use (polynomialOfCoeffs msg)
  simp
  ext i
  simp [ReedSolomon.evalOnPoints]

def makeZero (ι : ℕ) (F : Type*) [Zero F] : Fin ι → F := fun _ ↦ 0

@[simp]
lemma codewordIsZero_makeZero {ι : ℕ} {F : Type*} [Zero F] :
  makeZero ι F = 0 := by unfold makeZero; ext; rfl

/--
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Field F] {deg : ℕ} [inst : NeZero deg] (α : Fin ι ↪ F) :
  LinearCode.mulByGenMat (Vandermonde.nonsquare deg α) = ReedSolomon.code α deg := by
  unfold LinearCode.mulByGenMat ReedSolomon.code
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

lemma dim_eq_deg [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCode.dim (ReedSolomon.code α deg) = deg := by
  rw [← genMatIsVandermonde, ← LinearCode.dimEqRankGenMat, Vandermonde.nonsquareRank]
  simp [h]

lemma length_eq_domain_size [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCode.length (ReedSolomon.code α deg) = ι := by
  rw [LinearCode.length]

lemma rate [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCode.rate (ReedSolomon.code α deg) = deg / ι := by
  rw [LinearCode.rate, dim_eq_deg, length_eq_domain_size]
  exact h

lemma dist_le_length [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} :
    LinearCode.minDist (ReedSolomon.code α deg) ≤ ι := by
  simp [(@length_eq_domain_size ι F _ deg α).symm]
  exact LinearCode.minDist_UB

lemma card_le_lemma {α β : Type*} [DecidableEq α]
  {s : Multiset α} {s' : Multiset β} (f : α ↪ β) :
  (∀ a : α, s.count a ≤ s'.count (f a)) → s.card ≤ s'.card := by
  intros h
  rw [←Multiset.toFinset_sum_count_eq, ←Multiset.toFinset_sum_count_eq]
  have : Finset.image f s.toFinset ⊆ s'.toFinset := by
    intros a h'
    simp only [Finset.mem_image, Multiset.mem_toFinset] at h'
    rcases h' with ⟨b, b_in_s, f_b_eq_a⟩
    specialize h b
    rw [Multiset.mem_toFinset, ←f_b_eq_a]
    rw [←Multiset.count_pos] at b_in_s ⊢
    linarith
  apply @le_trans ℕ _ _ (∑ i ∈ Finset.image (⇑f) s.toFinset, Multiset.count i s')
  · rw [Finset.sum_image (by aesop)]
    apply Finset.sum_le_sum
    intros a _
    exact h a
  · have h' := @Finset.sum_le_sum_of_subset_of_nonneg β ℕ _ (fun a ↦ Multiset.count a s') _ _ this
    apply h'
    simp


open Finset in
/--
  The minimal code distance of an RS code of length `ι` and dimensio `deg` is `ι - deg + 1`
-/
theorem minDist [Field F] [Inhabited F] {deg ι : ℕ} {α : Fin ι ↪ F} [φ : NeZero deg] (h : deg ≤ ι) :
  LinearCode.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by
  have : NeZero ι := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ =>
     have distUB := LinearCode.singletonBound (ReedSolomon.code α deg)
     rw [length_eq_domain_size, dim_eq_deg h] at distUB
     have : LinearCode.minDist (ReedSolomon.code α deg) ≤ ι := dist_le_length
     omega
  case p₂ =>
    rw [LinearCode.minDist_eq_minWtCodewords]
    have lem1 {s : Set ℕ} (h : s.Nonempty) {a : ℕ} : (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
      exact fun a_1 ↦ ConditionallyCompleteLattice.le_csInf s a h a_1
    apply lem1
    · exists ι
      rw [Set.mem_setOf_eq]
      unfold ReedSolomon.code
      exists (fun _ ↦ 1)
      refine ⟨?_, ?_, ?_⟩
      · rw [Submodule.mem_map]
        exists (C 1)
        apply And.intro
        · rw [Polynomial.mem_degreeLT]
          simp only [map_one, degree_one, Nat.cast_pos]
          have := φ.out
          match deg with
          | .zero => simp at this
          | .succ _ => simp
        · unfold ReedSolomon.evalOnPoints
          simp only [map_one, LinearMap.coe_mk, AddHom.coe_mk, eval_one]
      · intros h
        have {α : Type} {β : Type u_1} {f g : α → β} : f = g → ∀ x : α, f x = g x := by
          aesop
        specialize @this (Fin ι) F (fun x ↦ 1) 0 h 0
        simp at this
      · unfold wt
        simp
    · intros b h
      rw [Set.mem_setOf_eq] at h
      rcases h with ⟨msg, msg_elem, msg_neq_0, wt_c_eq_b⟩
      unfold ReedSolomon.code at msg_elem
      rw [Submodule.mem_map] at msg_elem
      rcases msg_elem with ⟨p, p_deg, p_eval_on_α_eq_msg⟩
      have p_eval_on_α_eq_msg' : ∀ i, msg i = p.eval (α i) := by aesop
      have p_neq_0 : p ≠ 0 := by aesop
      have : p.natDegree < deg := by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree p_neq_0, Nat.cast_lt] at p_deg
        exact p_deg
      have α_i_mem_roots_of_msg_i_eq_0 : ∀ i, msg i = 0 → α i ∈ p.roots := by aesop
      unfold wt at wt_c_eq_b
      have msg_zeros_lt_deg : #{i | msg i = 0} < deg := by
        apply @lt_of_le_of_lt ℕ _ _ p.roots.card
        · have : #{i | msg i = 0} = (({i | msg i = 0} : Finset (Fin ι)).val).card := by rfl
          rw [this]
          apply card_le_lemma α
          intros i
          by_cases msg_i_eq_0 : msg i = 0
          · specialize α_i_mem_roots_of_msg_i_eq_0 _ msg_i_eq_0
            simp only [filter_val, msg_i_eq_0, Multiset.count_filter_of_pos, Multiset.count_univ,
              count_roots]
            rw [Nat.succ_le, Polynomial.rootMultiplicity_pos p_neq_0, ←Polynomial.mem_roots p_neq_0]
            assumption
          · simp [msg_i_eq_0]
        · exact lt_of_le_of_lt (Polynomial.card_roots' _) this
      have union_eq_univ :
        ({i | msg i = 0} : Finset (Fin ι)) ∪ ({i | msg i ≠ 0} : Finset (Fin ι)) = univ := by
        ext i
        simp only [ne_eq, mem_union, mem_filter, mem_univ, true_and, iff_true]
        exact Classical.em _
      have is_disj :
        Disjoint ({i | msg i = 0} : Finset (Fin ι)) ({i | msg i ≠ 0} : Finset (Fin ι)) := by
        apply disjoint_filter_filter_neg
      have union_card_eq_univ_card :
        #(({i | msg i = 0} : Finset (Fin ι)) ∪ ({i | msg i ≠ 0} : Finset (Fin ι))) =
          #(univ : Finset (Fin ι)) := by
        rw [union_eq_univ]
      have : #{i | msg i = 0} + #{i | msg i ≠ 0} = ι := by
        rw
          [
            Finset.card_union_of_disjoint is_disj,
            card_univ,
            Fintype.card_fin
          ] at union_card_eq_univ_card
        exact union_card_eq_univ_card
      have : #{i | msg i ≠ 0} > ι - deg  := by
        rw [Nat.eq_sub_of_add_eq' this]
        zify [h, show #{i | msg i = 0} ≤ ι from
          (by
            transitivity
            · apply Finset.card_le_card
              exact Finset.subset_univ _
            · simp
          )]; linarith
      rw [wt_c_eq_b] at this
      linarith

end ReedSolomonCode
end
