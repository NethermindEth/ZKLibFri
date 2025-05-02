import Mathlib.Data.Matrix.Rank
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Defs

open Classical

/--
  weight of a vector
-/
noncomputable def vector.wt {F : Type*} [Semiring F][Zero F] {ι : ℕ}
  (v : Fin ι → F) : ℕ  := Finset.card {i | v i ≠ 0}

namespace LinearCodes

noncomputable section

variable {ι : ℕ}
         {F : Type*} [Semiring F]

abbrev LinearCode.{u} (ι : ℕ) (F : Type u) [Semiring F] : Type u := Submodule F (Fin ι → F)

def minDist (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v = d }
end

noncomputable section

variable {ι κ : ℕ}
         {F : Type*} [CommRing F]

/--
A linear code of length `ι` defined by right multiplication by a `κ x ι` generator matrix `G`.
-/
def mul_GenMat (G : Matrix (Fin κ) (Fin ι) F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/--
A linear code of length `ι` defined by left multiplication by a `ι x κ` generator matrix `G`.
-/

def genMat_mul (G : Matrix (Fin ι) (Fin κ) F) : Submodule F (Fin ι → F) :=
  LinearMap.range G.mulVecLin


def dim (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma dimEqRankGenMat {G : Matrix (Fin κ) (Fin ι) F} :
  G.rank = dim (genMat_mul G) := by
  rw[Matrix.rank, dim, genMat_mul]

def length (LC : LinearCode ι F) := Fintype.card (Fin ι)

def rate (LC : LinearCode ι F) : ℚ :=
  (dim LC : ℚ) / (length LC : ℚ)

/--
`ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

def minWtCodewords (LC : LinearCode ι F) : ℕ :=
  sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ vector.wt c = w}

lemma distToWt (u v : Fin ι → F) :
  hammingDist u v = vector.wt (u - v) := by
  rw[hammingDist, vector.wt]
  congr 1
  simp only [Pi.sub_apply]
  ext i
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [@sub_eq_iff_eq_add, zero_add]


/--
The min distance of a linear code `LC` equals to the minimum of the weights of non-zero codewords.
-/
lemma minDistEqMinWt (LC : LinearCode ι F) :
  minDist LC = minWtCodewords LC := by
  rw[minDist, minWtCodewords]
  congr 1
  ext d
  simp only [ne_eq, Set.mem_setOf_eq]
  constructor
  rintro ⟨u,hu,v,hv,hunv,hd⟩
  rw[distToWt] at hd
  refine ⟨u - v, Submodule.sub_mem LC hu hv, ?_, hd⟩
  rw[sub_eq_zero]
  exact hunv

  intro h
  rcases h with ⟨c, hc, hwt⟩
  exists c
  apply And.intro hc
  exists 0
  apply And.intro (Submodule.zero_mem _)
  apply And.intro hwt.1
  rw[distToWt, sub_zero]
  exact hwt.2

theorem singletonBound (LC : LinearCode ι F) :
  dim LC ≤ length LC - minDist LC + 1 := by sorry

end
end LinearCodes
