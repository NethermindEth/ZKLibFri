import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.LinearCodes
import ArkLib.Data.CodingTheory.RelativeHammingDistance

open Classical


noncomputable section

variable {ι : ℕ}
         {F : Type*}

abbrev Code.{u} (ι : ℕ) (S : Type u) : Type u := Set (Fin ι → S)

/--
Hamming ball of radius `r` centred at a word `y`.
-/
def hammingBall (C : Code ι F) (y : Fin ι → F) (r : ℕ) : Set (Fin ι → F) :=
  { c | c ∈ C ∧ hammingDist y c ≤ r }
/--
Ball of radius `r` centred at a word `y` with respect to the relative Hamming distance.
-/
def relHammingBall (C : Code ι F) (y : Fin ι → F) (r : ℝ)  : Set (Fin ι → F) :=
  { c | c ∈ C ∧ relHammingDist y c ≤ r }

/--
The number of close codewords to a given word `y` with respect to the Hamming distance metric.
-/
def listOfCloseCodewords (C : Code ι F) (y : Fin ι → F) (r : ℕ) : ℕ∞ :=
  { c | c ∈ C ∧ hammingDist y c ≤ r }.encard

/--
The number of close codewords to a given word `y` with respect to the relative Hamming
distance metric.
-/
def listOfCloseCodewordsRel (C : Code ι F) (y : Fin ι → F) (r : ℝ) : ℕ∞ :=
  { c | c ∈ C ∧ relHammingDist y c ≤ r }.encard

/--
Definition of `(r,ℓ)`-list decodable code.
-/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℕ) : Prop :=
  ∀ y : Fin ι → F, listOfCloseCodewordsRel C y r ≤ ℓ

end
