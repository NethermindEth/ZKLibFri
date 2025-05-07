import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Rank

open Classical

noncomputable section

variable {F : Type*} [Semiring F]
variable {κ ι : ℕ}

namespace Affine

/--
affine line between u and v
-/
def line [Ring F] (u v : Fin ι → F) : Set (Fin ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine

namespace Matrices

def neqCols (U V : Matrix (Fin κ) (Fin ι) F) : Finset (Fin ι) :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

def rowSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F (Fin ι → F) :=
  Submodule.span F {U i | i : Fin κ}

def rowRank (U : Matrix (Fin κ) (Fin ι) F) : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F (Fin κ → F) :=
  Submodule.span F {Matrix.transpose U i | i : Fin ι}

def colRank (U : Matrix (Fin κ) (Fin ι) F) : ℕ :=
  Module.finrank F (colSpan U)

lemma rank_eq_min_row_col_rank [CommRing F] (U : Matrix (Fin κ) (Fin ι) F) :
  U.rank = min (rowRank U) (colRank U) := by sorry



end Matrices
