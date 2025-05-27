/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Defs

namespace FinEnum

@[simp]
private lemma length_toList {α : Type*} [FinEnum α] :
  (FinEnum.toList α).length = FinEnum.card α := by
  simp [FinEnum.toList]

def fnOfLE (ι θ : Type*) [FinEnum ι] [FinEnum θ] (h : FinEnum.card ι ≤ FinEnum.card θ) :
  ι → θ := fun i ↦ let ⟨σᵢ, hσᵢ⟩ := FinEnum.equiv.toFun i
                   let σ := FinEnum.toList θ
                   have : σᵢ < σ.length := by aesop (add safe apply lt_of_lt_of_le)
                   σ.get ⟨σᵢ, this⟩

lemma injective_fnOfLE {ι : Type*} [FinEnum ι] {α : Type*} [FinEnum α]
  (h : FinEnum.card ι ≤ FinEnum.card α) : Function.Injective (fnOfLE ι α h) := fun a b h' ↦ by
  have : (toList α)[(equiv a).val]? = (toList α)[(equiv b).val]? := by
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]; simpa
  apply List.getElem?_inj (by aesop (add safe apply lt_of_lt_of_le)) (by simp) at this
  rwa [Fin.val_inj, EmbeddingLike.apply_eq_iff_eq] at this

def fnOfFinFun {α ι : Type*} [FinEnum ι] (n : ℕ) (h : n ≤ FinEnum.card ι) (f : ι → α) :
  Fin n → α := fun ⟨i, hi⟩ ↦ let σ := FinEnum.toList ι
                             have : i < σ.length := by aesop (add safe apply lt_of_lt_of_le)
                             f (σ.get ⟨i, this⟩)

lemma injective_fnOfFinFun {ι : Type*} [FinEnum ι] {α : Type*} [FinEnum α] {f : ι → α} {n : ℕ}
  (inj : Function.Injective f) (h : n ≤ FinEnum.card ι) :
  Function.Injective (fnOfFinFun n h f) := fun a b h' ↦ by
  simp [fnOfFinFun] at h'
  apply inj at h'
  have : (toList ι)[a.val]? = (toList ι)[b.val]? := by
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]; simpa
  apply List.getElem?_inj (by aesop (add safe apply lt_of_lt_of_le)) (by simp) at this
  rwa [Fin.val_inj] at this

end FinEnum

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

def subUpFull {m : Type*} [FinEnum m]
              {n : Type*} [FinEnum n]
              (U : Matrix m n F) (h_col : FinEnum.card n ≤ FinEnum.card m) :
  Matrix n n F := Matrix.submatrix U (FinEnum.fnOfFinFun _ h_col id ∘ FinEnum.equiv) id
  -- FinEnum.fnOfFinFun _ _ _
  -- fun k ↦
  --   let ⟨σᵢ, hσᵢ⟩ := FinEnum.equiv.toFun k
  --   let σ := FinEnum.toList m
  --   have : σᵢ < σ.length := by aesop (add safe apply lt_of_lt_of_le)
  --   σ.get ⟨σᵢ, this⟩
                    
lemma full_col_rank_via_rank_subUpFull {m : Type*} [FinEnum m] {n : Type*} [FinEnum n] [CommRing F]
  {U : Matrix m n F} (h_col : FinEnum.card n ≤ FinEnum.card m) :
  U.rank = Fintype.card n ↔ (subUpFull U h_col).rank = Fintype.card n := by sorry

def subLeftFull (U : Matrix (Fin m) (Fin n) F) (h_row : m ≤ n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id (Fin.castLE h_row)

lemma full_row_rank_via_rank_subLeftFull [CommRing F] {U : Matrix (Fin m) (Fin n) F}
  (h_row : m ≤ n) :
  U.rank = m ↔ (subLeftFull U h_row).rank = m := by sorry

end Matrix

end

section
variable {F : Type*} {ι : Type*}

namespace Affine

/--
affine line between vectors `u` and `v`.
-/
def line {F : Type*} {ι : Type*} [Ring F] (u v : ι → F) : Set (ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine
end
