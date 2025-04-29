import ArkLib.Data.CodingTheory.LinearCodes
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.RelativeHammingDistance

open Classical

variable {ι : ℕ}
         {F : Type*} [Semiring F]
         {C : Set (Fin ι → F)}

abbrev LinearCode.{u} (F : Type u) [Semiring F] : Type u := Submodule F ((Fin ι) → F)

noncomputable section

namespace Vandermonde
/--
  `ι x deg` Vandermonde matrix
-/
def nonsquare {deg : ℕ} (α : Fin ι ↪ F) : Matrix (Fin ι) (Fin deg) F :=
  Matrix.of (fun i j => (α i) ^ j.1)

/--
  The transpose of a `ι x deg` Vandermonde matrix
-/
def nonsquareTranspose [Field F] {deg : ℕ} (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare α).transpose

end Vandermonde

namespace ReedSolomonCode

/--
The transposed of the  Vandermonde matrix is the generator matrix for an RS code of length n and dimension deg.
-/
lemma genMatIsVandermondeT [Field F] {deg : ℕ} (α : Fin ι ↪ F) :
  C(Vandermonde.nonsquareTranspose (deg := deg) α) = ReedSolomon.code α deg := by sorry

/--
  The minimal code distance of an RS code of length n and dim deg is n - deg + 1
-/
lemma minDist [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  RelativeHamming.codeDistLin (ReedSolomon.code α deg) = ι - deg + 1 := sorry


lemma dim [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.dimLinCode (ReedSolomon.code α deg) = deg := sorry

/--
rate of RS code
-/
def rate [Field F] (deg : ℕ) (α : Fin ι ↪ F) : ℚ :=
  LinearCodes.rateCode (ReedSolomon.code α deg)

end ReedSolomonCode
end
