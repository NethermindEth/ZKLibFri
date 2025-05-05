/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Defs

noncomputable section

variable {F : Type*} [Semiring F]
variable {m n : ℕ}

namespace Matrix

def neqCols [DecidableEq F] (U V : Matrix (Fin m) (Fin n) F) : Finset (Fin n) :=
  {j | ∃ i : (Fin m), V i j ≠ U i j}

def rowSpan (U : Matrix (Fin m) (Fin n) F) : Submodule F (Fin n → F) :=
  Submodule.span F {U i | i : Fin m}

def rowRank (U : Matrix (Fin m) (Fin n) F) : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan (U : Matrix (Fin m) (Fin n) F) : Submodule F (Fin m → F) :=
  Submodule.span F {Matrix.transpose U i | i : Fin n}

def colRank (U : Matrix (Fin m) (Fin n) F) : ℕ :=
  Module.finrank F (colSpan U)

lemma rank_eq_min_row_col_rank [CommRing F] {U : Matrix (Fin m) (Fin n) F} :
  U.rank = min (rowRank U) (colRank U) := by sorry

-- this really should be in mathlib?!
lemma full_rank_iff_det_ne_zero [CommRing F] {n : ℕ} {U : Matrix (Fin n) (Fin n) F} :
  U.rank = n ↔ Matrix.det U ≠ 0 := by sorry

def subUpFull (U : Matrix (Fin m) (Fin n) F) (h_col : n ≤ m) :
  Matrix (Fin n) (Fin n) F := Matrix.submatrix U (Fin.castLE h_col) id

lemma full_col_rank_via_rank_subUpFull [CommRing F] {U : Matrix (Fin m) (Fin n) F}
  (h_col : n ≤ m) :
  U.rank = n ↔ (subUpFull U h_col).rank = n := by sorry

def subLeftFull (U : Matrix (Fin m) (Fin n) F) (h_row : m ≤ n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id (Fin.castLE h_row)

lemma full_row_rank_via_rank_subLeftFull [CommRing F] {U : Matrix (Fin m) (Fin n) F}
  (h_row : m ≤ n) :
  U.rank = m ↔ (subLeftFull U h_row).rank = m := by sorry

end Matrix

end

section
variable {F : Type*} [Semiring F]
         {ι : ℕ}

namespace Embedding

def restrictionToFun (deg : ℕ) (α : Fin ι ↪ F) (h : deg ≤ ι) : Fin deg → F :=
  α.toFun ∘ Fin.castLE h

/--
The composition of an embedding and the canonical embedding is injective.
-/
lemma restrictionToFun_injective {deg : ℕ} {α : Fin ι ↪ F}
  (h : deg ≤ ι) :
  Function.Injective (Embedding.restrictionToFun deg α h) := by
  unfold restrictionToFun
  simp only [Function.Embedding.toFun_eq_coe, EmbeddingLike.comp_injective]
  exact Fin.castLE_injective h

end Embedding

namespace Affine

/--
Affine line between two vectors with coefficients in a semiring.
-/
def line [Ring F] (u v : Fin ι → F) : Set (Fin ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine
