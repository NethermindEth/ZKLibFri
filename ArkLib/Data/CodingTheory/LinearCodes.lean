/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Data.Matrix.Rank
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Defs

/-!
  Definition of a linear code, minimal distance of a linear code, length, dimension and rate.
  Linear codes defined by a generator matrices and rephrase of dimension in this framework.
  Definition of the weight of a vector, statement and proof of the fact that the minimal
  distance of a linear code equals the minimal weight taken over the set of codewords.
-/

open Classical
open Finset

noncomputable def wt {F : Type*} [Semiring F] [Zero F] {ι : Type*} [Fintype ι]
  (v : ι → F) : ℕ := #{i | v i ≠ 0}

namespace LinearCodes

noncomputable section

variable {F : Type*} [Semiring F]
         {ι : Type*} [Fintype ι]

abbrev LinearCode.{u, v} (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] : Type (max u v) :=
  Submodule F (ι → F)

def minDist (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v = d }

end

noncomputable section

variable {ι : Type*} [Fintype ι]
         {κ  : Type*} [Fintype κ]
         {F : Type*} [CommRing F]

/--
A linear code of length `ι` defined by right multiplication by a `κ x ι` generator matrix `G`.
-/
def mul_GenMat (G : Matrix κ ι F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/--
A linear code of length `ι` defined by left multiplication by a `ι x κ` generator matrix `G`.
-/
def genMat_mul (G : Matrix ι κ F) : Submodule F (ι → F) :=
  LinearMap.range G.mulVecLin

def dim (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma dimEqRankGenMat {G : Matrix κ ι F} :
  G.rank = dim (genMat_mul G) := rfl

def length (LC : LinearCode ι F) := Fintype.card ι

def rate (LC : LinearCode ι F) : ℚ :=
  (dim LC : ℚ) / (length LC : ℚ)

/--
`ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

def minWtCodewords (LC : LinearCode ι F) : ℕ :=
  sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ wt c = w}

lemma hammingDist_eq_wt_sub {u v : ι → F} : hammingDist u v = wt (u - v) := by
  aesop (add simp [hammingDist, wt, sub_eq_zero])

/--
The min distance of a linear code `LC` equals to the minimum of the weights of non-zero codewords.
-/
lemma minDist_eq_minWtCodewords {LC : LinearCode ι F} : minDist LC = minWtCodewords LC := by
  unfold minDist minWtCodewords
  refine congrArg _ (Set.ext fun _ ↦ ⟨fun ⟨u, _, v, _⟩ ↦ ⟨u - v, ?p₁⟩, fun _ ↦ ⟨0, ?p₂⟩⟩) <;>
  aesop (add simp [hammingDist_eq_wt_sub, sub_eq_zero])

/--
Singleton Bound Theorem.
-/
theorem singletonBound (LC : LinearCode ι F) :
  dim LC ≤ length LC - minDist LC + 1 := by sorry

end
end LinearCodes
