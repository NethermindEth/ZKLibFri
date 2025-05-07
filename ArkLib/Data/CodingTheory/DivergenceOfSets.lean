import ArkLib.Data.CodingTheory.RelativeHammingDistance

namespace DivergenceOfSets

noncomputable section

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {U V C : Set (ι → F)}

/--
`d_U` is the set of achievable relative Hamming distances between elements `u ∈ U` and `V`
-/
def d_U [Nonempty ι] (U V : Set (ι → F)) : Set ℚ :=
  { d : ℚ | ∃ u ∈ U, δᵣ(u,V) = d }

@[simp]
lemma d_U_subset_RelHammingDistRange [Nonempty ι] :
d_U U C ⊆ RelativeHamming.RelHammingDistRange ι :=
  λ _ _ ↦ by aesop (add simp d_U)

@[simp]
lemma finite_d_U [Nonempty ι] : (d_U U V).Finite :=
  Set.Finite.subset RelativeHamming.finite_relHammingDistRange d_U_subset_RelHammingDistRange

/--
divergence of the arbitrary set `U` to the arbitrary set `V`
-/
def div_U_from_V [Nonempty ι] (U : Set (ι → F)) (V : Set (ι → F)) : ℚ :=
  have : Fintype (d_U U V) := @Fintype.ofFinite _ finite_d_U
  if h : (d_U U V).Nonempty
  then (d_U U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

  end

  end DivergenceOfSets
