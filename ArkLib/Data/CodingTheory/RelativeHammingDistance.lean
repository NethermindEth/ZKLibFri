import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas

namespace RelativeHamming

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

@[simp]
lemma zero_lt_card [Nonempty ι] : 0 < Fintype.card ι := by have := Fintype.card_ne_zero (α := ι); omega

abbrev LinearCode.{u, v} (ι : Type u) (F : Type v) [Semiring F] : Type (max u v) := Submodule F (ι → F)

noncomputable section

/--
  definition of distance of a linear code
-/
def codeDistLin [Semiring F] (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d }

section

variable [Nonempty ι]

/--
  relative Hamming Distance between vectors/codewords u and v
-/
def relHammingDist (u v : ι → F) : ℚ :=
  (hammingDist u v : ℚ) / (Fintype.card ι : ℚ)

@[simp]
lemma relHammingDist_le_one : relHammingDist u v ≤ 1 := by
  unfold relHammingDist
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

@[simp]
lemma zero_le_relHammingDist : 0 ≤ relHammingDist u v := by
  unfold relHammingDist
  rw [le_div_iff₀ (by simp)]
  simp

end

/--
δᵣ(u,v) denotes the relative Hamming distance between vectors u and v
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/--
range of the relative Hamming distance
-/

def RelHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ :=
  { d : ℚ | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι }

@[simp]
lemma relHammingDist_mem_RelHammingDistRange : δᵣ(u, v) ∈ RelHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

/--
The range of the relative Hamming distance is a bounded set
-/

@[simp]
lemma finite_relHammingDistRange [Nonempty ι] : (RelHammingDistRange ι).Finite := by
  simp only [RelHammingDistRange, ← Set.finite_coe_iff, Set.coe_setOf]
  exact
    finite_iff_exists_equiv_fin.2
      ⟨Fintype.card ι + 1,
        ⟨⟨
        λ ⟨s, _⟩ ↦ ⟨(s * Fintype.card ι).num.toNat, by aesop (add safe (by omega))⟩,
        λ n ↦ ⟨n / Fintype.card ι, by use n; simp; omega⟩,
        λ ⟨_, _, _, h₂⟩ ↦ by field_simp [h₂],
        λ _ ↦ by simp
        ⟩⟩
      ⟩

/--
There are finitely many distinct pairs in a linear code C over a finite semiring F
-/
@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

/--
The set of possible distances between distinct elements of a code C
-/
def d_C (C : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ p ∈ Set.offDiag C, δᵣ(p.1, p.2) = d }

section

@[simp]
lemma d_C_subset_RelHammingDistRange : d_C C ⊆ RelHammingDistRange ι :=
  λ _ _ ↦ by aesop (add simp d_C)

@[simp]
lemma finite_d_C [Nonempty ι] : (d_C C).Finite :=
  Set.Finite.subset finite_relHammingDistRange d_C_subset_RelHammingDistRange

end

/--
relative Hamming Distance of a code C over a semiring F
-/
def relHammingDistOfCode [Nonempty ι] (C : Set (ι → F)) : ℚ :=
  have : Fintype (d_C C) := @Fintype.ofFinite _ finite_d_C
  if h : (d_C C).Nonempty
  then (d_C C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
δᵣ(C) denoted the minimum relative Hamming distance of a code C
-/
notation "δᵣ(" C ")" => relHammingDistOfCode C

/--
d_w is the set of all possible relative Hamming distances between a vector w and a code C
-/
def d_w (w : ι → F) (C : Set (ι → F)) : Set ℚ :=
  {d : ℚ | ∃ c ∈ C, c ≠ w ∧ δᵣ(w, c) = d}

@[simp]
lemma d_w_subset_RelHammingDistRange : d_w w C ⊆ RelHammingDistRange ι :=
  λ d h ↦ by aesop (add simp d_w)

@[simp]
lemma finite_d_w [Nonempty ι] : (d_w w C).Finite :=
  Set.Finite.subset finite_relHammingDistRange d_w_subset_RelHammingDistRange

instance [Nonempty ι] : Fintype (d_w w C) := @Fintype.ofFinite _ finite_d_w

/--
  Counter example to d_wNonempty,
  need an extra condition that C has at least two elements or
  w isn't in C and C is non-empty?
-/
example : d_w w {w} = ∅ := by
  unfold d_w
  simp

/--
relative Hamming distance between a vector w and a code C
-/

def relHammingDistToCode [Nonempty ι] (w : ι → F) (C : Set (ι → F)) : ℚ :=
  if h : (d_w w C).Nonempty
  then (d_w w C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

/--
δᵣ(w,C) denotes the relative distance between a vector w and a code C
-/
notation "δᵣ(" w ", " C ")" => relHammingDistToCode w C


@[simp]
lemma zero_mem_RelHammingDistRange : 0 ∈ RelHammingDistRange ι := by use 0; simp

@[simp]
lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] :
  δᵣ(c, C) ∈ RelHammingDistRange ι := by
  unfold relHammingDistToCode
  split_ifs
  · exact Set.mem_of_subset_of_mem (s₁ := (d_w c C).toFinset) (by simp) (Finset.min'_mem _ _)
  · simp


/--
  weight of a vector/codeword
-/
def wt [Zero F] (v: ι → F) : Finset ι := {i | v i ≠ 0}

end
end RelativeHamming
