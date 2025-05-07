import Mathlib.Data.Matrix.Rank

namespace LinearCodes

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {C : Set (ι → F)}

abbrev LinearCode.{u, v} (ι : Type u) (F : Type v) [Semiring F] : Type (max u v) := Submodule F (ι → F)

noncomputable section
/--
A linear code of length n is defined by a k x n generating matrix
-/
def codeByGenMatrix' {k : Type*} [Fintype k] [Semiring F] (G : Matrix k ι F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/--
C(G) denotes the code corresponding to the generating matrix G
-/
notation "C(" G ")" => LinearCodes.codeByGenMatrix' G

/--
 Definition of the dimension of a linear code C
-/
def dimLinCode {ι : Type*} [Semiring F] (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
dimC(C) denotes the dimension of a linear code C
 -/
notation "dimC(" LC ")" => dimLinCode LC

/--
The dimension of a linear code equals the rank of its associated generating matrix
-/
lemma dimLinCodeByGenMatrix {k : Type*} [Fintype k] [CommRing F] {G : Matrix k ι F} :
  dimC(C(G)) = G.rank := sorry


/--
Length of a linear code C
-/
def lengthCode [CommRing F] (LC : LinearCode ι F) := Fintype.card ι

/--
len(C) denotes the length of a linear code C
-/
notation "lenC(" C ")" => lengthCode C

/--
rate of a linear code
-/
def rateCode [CommRing F] (LC : LinearCode ι F) : ℚ :=
  (dimC(LC) : ℚ) / (lenC(LC) : ℚ)

/--
ρ(C) denotes the rate of a linear code C
--/
notation "ρ(" LC ")" => rateCode LC

end

end LinearCodes
