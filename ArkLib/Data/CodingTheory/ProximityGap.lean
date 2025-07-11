import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes"

  ## Main Definitions

-/

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
def proximityMeasure (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityMeasure C u v d > bound)
    → (Δ₀( u ⋈ v , C ^⋈ Fin 2 ) ≤ d)

/-- A code `C` exhibits `δ`-correlated agreement with respect to a tuple of vectors `W_1, ..., W_k`
  if there exists a set `S` of coordinates such that the size of `S` is at least `(1 - δ) * |n|`,
  and there exists a tuple of codewords `v_1, ..., v_k` such that `v_i` agrees with `W_i` on `S`
  for all `i`. -/
def correlatedAgreement (C : Set (n → F)) (δ : ℝ≥0) {k : ℕ} (W : Fin k → n → F) : Prop :=
  ∃ S : Finset n, #(S) ≥ (1 - δ) * (Fintype.card n) ∧
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} ⊆ S

end

section

variable {α : Type*}[DecidableEq α] [Nonempty α]
         {ι : Type*}
         {F : Type*}

/--
Distance from a point `x` to a set of points `P`.
-/
noncomputable def distToSet (Δ : (ι → α) → (ι → α) → ℕ) (x : ι → α) (P : Set (ι → α)) : ℕ :=
  sInf {d | ∃ y ∈ P, Δ x y = d}

/--
Definition 1.1 in [BCIKS20].
-/
noncomputable def generalProximityGap (P : Finset (ι → α)) (C : Finset (Finset (ι → α)))
 (Δ : (ι → α) → (ι → α) → ℕ) (δ ε : ℝ≥0) (S : Finset (ι → α)) (h' : S ∈ C) (h : S.Nonempty)
  : Prop :=
  (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} = 1
  ∨ (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} ≤ ε

/--
A collection of affine spaces in an `F`-module is non-empty.
-/
lemma setOfAffineSubspaces_nonempty [Ring F] :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Nonempty := by simp only [exists_eq', Set.setOf_true,
    Set.univ_nonempty]

/--
A collection of affine spaces over a finite `F`-module is finite.
-/
lemma setOfAffineSubspaces_finite [Ring F] [Fintype F] [Fintype ι] :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Finite := by
  simp only [exists_eq', Set.setOf_true]
  exact Set.finite_univ

/--
The pair of proximity and error parameter `(δ,ε)` for Reed-Solomon codes defined up to the Johnson
bound. More precisely, let `ρ` be the rate of the Reed-Solomon code. Then for `δ ∈ (0, 1 - √ρ)`,
we define the relevant error parameter `ε` for the unique decoding bound, i.e. `δ ∈ [0, (1-√ρ)/2]`
and Johnson bound, i.e. `δ ∈ [(1-√ρ)/2 , 1 - √ρ]`.
-/
noncomputable def proximityParams [Field F] [Fintype F] [Fintype ι] (δ : ℝ≥0) (deg : ℕ)
  (domain : ι ↪ F) : ℝ≥0 :=
  if UD : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)/2 then Fintype.card ι / Fintype.card F
  else if JB : δ ≥ 1 - (ReedSolomonCode.sqrtRate deg domain)/2 ∧ δ ≤ 1 -
  (ReedSolomonCode.sqrtRate deg domain)
    then
    let m := min (1 - (ReedSolomonCode.sqrtRate deg domain) - δ)
                (ReedSolomonCode.sqrtRate deg domain/ 20)
    ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
    else 0

-- /--
-- Theorem 1.2 (Proximity gap for RS codes)
-- -/
-- theorem proximityGapsRSCode [Fintype ι] [Nonempty ι] [Field F] [Fintype F]

/--
Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
-/
theorem correlatedAgreement_lines [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
(u : Fin 2 → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype F).toOuterMeasure
    {z | Code.relHammingDistToCode (u 1 + z • u 2) (ReedSolomon.code domain deg) ≤ δ}
      > proximityParams δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/--
Let `u := {u_1, ..., u_l}` be a collection of vectors with coefficients in a semiring.
The parameterised curve of degree `l` generated by `u` is the set of linear combinations of the
form `{∑ i ∈ l r ^ i • u_i | r ∈ F}`.
-/
def parametrisedCurve {l : ℕ} [Semiring F]
  (u : Fin l → ι → F) : Set (ι → F) := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
         {F : Type*} [Semiring F] [DecidableEq F]
/--
A parametrised curve over a finite field is finite.
-/
def parametrisedCurveFinite [Fintype F]
 {l : ℕ} (u : Fin l → ι → F) :
Finset (ι → F) := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}


instance [Fintype F] [Nonempty F] {l : ℕ} :
  ∀ u : Fin l → ι → F, Nonempty {x // x ∈ parametrisedCurveFinite u } := by
  intro u
  unfold parametrisedCurveFinite
  simp only [mem_filter, mem_univ, true_and, nonempty_subtype]
  obtain ⟨r⟩ := ‹Nonempty F›
  use ∑ i : Fin l, r ^ (i : ℕ) • u i, r


/--
Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in in [BCIKS20].
-/
theorem correlatedAgreement_affine_curves [Nonempty ι][Field F] [Fintype F]
{l : ℕ} (u : Fin l → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype (parametrisedCurveFinite u)).toOuterMeasure
    {y | Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}
    > l*(proximityParams δ deg domain)):
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry




instance {l : ℕ} [NeZero l] : Nonempty (Fin l) := inferInstance

instance {l : ℕ} [NeZero l] : Fintype (Fin l) := inferInstance


instance {α : Type} [Fintype α] [Nonempty α] :
  Nonempty (Finset.univ : Finset α) :=
  by exact Nonempty.to_subtype (univ_nonempty_iff.mpr (by assumption))


def finsetVectorsU {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Finset (ι → F) :=
  Finset.univ.image u

def setVectorsU {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Set (ι → F) :=
  Finset.toSet (finsetVectorsU u)

theorem thing₁ {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  (finsetVectorsU u).Nonempty := by simp [finsetVectorsU]

instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  Nonempty (finsetVectorsU u) := by
  have := thing₁ (u := u)
  simp only [nonempty_subtype]
  exact this

instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  Nonempty (setVectorsU u) := by
  have := thing₁ (u := u)
  simp only [nonempty_subtype]
  exact this

theorem thing₁' {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  (setVectorsU u).Nonempty := by
  simp [setVectorsU]
  exact thing₁


#check affineSpan_nonempty



theorem thing₂ {F P V : Type*} [AddCommGroup V] [Ring F] [Module F V] {s : Set P}
  (h : Set.Nonempty s)
               [AddTorsor V P] : Nonempty ↥(affineSpan F s) := by
  have := @affineSpan_nonempty F V P _ _ _ _ s
  unfold Set.Nonempty at this h
  simp
  symm at this
  apply this.1
  exact h

-- def affineSpaceOnU {k : ℕ} [Fintype ι] [Field F] (u : Fin k → ι → F) :
-- AffineSubspace F (setVectorsU u) := affineSpan F (setVectorsU u)

theorem affineSpanUNonempty {F : Type*} [Field F][DecidableEq F] {k : ℕ} [Fintype ι]
  (u : Fin k → ι → F) : Nonempty ↥(affineSpan F (setVectorsU u)) := by

  sorry
  ---have := @affineSpan_nonempty F (setVectorsU u)

theorem thing₄' {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
  (u : Fin k → ι → F) : Finite ↥(affineSpan F (setVectorsU u)) := by
  unfold affineSpan
  infer_instance


-- theorem thing₄ {α P V : Type*} [AddCommGroup V] [Fintype α] [Ring α] [Module α V] [Fintype P]
--   {s : Finset P}
--            [AddTorsor V P] : Finite ↥(@affineSpan α V P _ _ _ _ s) := by
--   unfold affineSpan
--   infer_instance

noncomputable def thing₃' {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
  (u : Fin k → ι → F) : Fintype ↥(affineSpan F (setVectorsU u)) := by
  apply Fintype.ofFinite


-- noncomputable def thing₃ {α P V : Type*} [Fintype α] [AddCommGroup V]
--                                          [Ring α] [Module α V] [Fintype P] {s : Finset P}
--            [AddTorsor V P] : Fintype ↥(@affineSpan α V P _ _ _ _ s) := by
--   have := @thing₄ α P V _ _ _ _ _ s _
--   apply Fintype.ofFinite

theorem correlatedAgreement_affine_spaces [Fintype ι] [Field F] [Fintype F]
  [DecidableEq F] [Nonempty F] [Nonempty ι]
  {k : ℕ} (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity : (PMF.uniformOfFintype (affineSpan F (setVectorsU u))).toOuterMeasure
  {y | Code.relHammingDistToCode y (ReedSolomon.code domain deg) ≤ δ}
  > proximityParams δ deg domain) :
 correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry



-- def X (n : ℕ) : Type := {x : ℕ // x < n}

-- def eq {n : ℕ} : X n ≃ Fin n := sorry

-- #check Fin.add_one_le_of_lt

-- instance {n : ℕ} : Preorder (X n) where
--   le a b := eq a ≤ eq b
--   le_refl := λ _ ↦ Fin.le_refl _
--   le_trans := λ _ _ _ ↦ Fin.le_trans

-- instance {n : ℕ} : Add (X n) := Equiv.add eq

-- instance {n : ℕ} [NeZero n] {i : ℕ} : OfNat (X n) i where
--   ofNat := eq.symm (Fin.ofNat n i)

-- theorem abc {n : ℕ} {a b : X (n + 1)} (h : a < b) : a + 1 ≤ b := by
--   unfold LE.le
--   unfold_projs
--   simp
--   apply Fin.add_one_le_of_lt
--   unfold LT.lt at h
--   unfold_projs at h
--   simp at h
--   exact h.2






-- theorem correlatedAgreement_affine_spaces [Fintype ι] [Field F] [Fintype F]
--   [DecidableEq F] [AddTorsor F (ι → F)][Nonempty F] [Nonempty ι]
--   {k : ℕ} [NeZero k] (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
--   (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
--   (hproximity : (PMF.uniformOfFintype (affineSpan F (setVectorsU u))).toOuterMeasure
--   {y | Code.relHammingDistToCode y (ReedSolomon.code domain deg) ≤ δ}
--   > proximityParams δ deg domain) :
--  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

-- theorem correlatedAgreement_affine_spaces' [Fintype ι] [Field F] [Fintype F]
--   [DecidableEq F] [AddTorsor F (ι → F)]
--   {k : ℕ} [NeZero k] (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
--   (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
--     (hproximity : PMF.toOuterMeasure
--                     (@PMF.uniformOfFintype
--                       (@affineSpan F F (ι → F) _ _ _ _ (thing u))
--                       (@thing.thing₃ F (ι → F) F _ _ _ _ _ (thing u) _)
--                       (@thing.thing₂ F (ι → F) F _ _ _ (thing u)
--                                        (@thing.thing₁ F ι _ k _ _ u) _)) > sorry) : False := by sorry

end
