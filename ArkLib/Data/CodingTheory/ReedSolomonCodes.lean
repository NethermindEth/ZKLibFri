import CodingTheory.RelativeHammingDistance
import CodingTheory.LinearCodes
import ArkLib.Data.CodingTheory.ReedSolomon

namespace RSCodes

open Classical

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {C : Set (ι → F)}

abbrev LinearCode.{u, v} (ι : Type u) (F : Type v) [Semiring F] : Type (max u v) := Submodule F (ι → F)

noncomputable section

/--
  n x deg Vandermonde matrix
-/
def vandermonde_nonsq [Semiring F] {deg : ℕ} {n : ℕ} (α : Fin n ↪ F) : Matrix (Fin n) (Fin deg) F :=
  Matrix.of (fun i j => (α i) ^ j.1)

/--
  The transpose of an n x deg Vandermonde matrix
-/
def transpose_vandermonde_nonsq [Field F] {deg : ℕ} {n : ℕ} (α : Fin n ↪ F) :
  Matrix (Fin deg) (Fin n) F :=
  (vandermonde_nonsq α).transpose

/--
  The transposed Vandermonde matrix is the generator matrix for an RS code of length n and dimension deg.
  Hence, RS codes are linear codes.
-/
lemma vandermondeIsGenOfRS' [Field F] {deg : ℕ} {n : ℕ} (α : Fin n ↪ F) :
  C(transpose_vandermonde_nonsq (deg := deg) α) = ReedSolomon.code α deg := sorry

/--
  The minimal code distance of an RS code of length n and dim deg is n - deg + 1
-/
lemma minCodeDistRS [Field F] (deg : ℕ) {n : ℕ} (α : Fin n ↪ F) :
  RelativeHamming.codeDistLin (ReedSolomon.code α deg) = n - deg + 1 := sorry

/--
 The dimension of an RS code is deg
-/
lemma dimRSCode [Field F] {deg : ℕ} {n : ℕ} {α : Fin n ↪ F} :
  LinearCodes.dimLinCode (ReedSolomon.code α deg) = deg := sorry

/--
rate of RS code
-/
def rateRS [Field F] (deg : ℕ) {n : ℕ} (α : Fin n ↪ F) : ℚ :=
  LinearCodes.rateCode (ReedSolomon.code α deg)

end
end RSCodes
