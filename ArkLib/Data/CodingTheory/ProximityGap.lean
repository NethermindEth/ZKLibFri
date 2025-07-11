import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Set.Defs


/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  ## Main Definitions

-/

open NNReal Finset Function

open scoped BigOperators

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


section

variable {α : Type*}[DecidableEq α] [Nonempty α]
         {ι : Type*} [DecidableEq ι] [Nonempty ι]


/--
Distance from a point to a set of points.
-/
noncomputable def distToSet (Δ : (ι → α) → (ι → α) → ℝ≥0) (x : ι → α) (P : Set (ι → α)) : ℝ≥0 :=
  sInf {d | ∃ y ∈ P, Δ x y = d}


/--
Definition 1.1 in Proximity Gaps paper.
KATY TO DO: maybe `δ : ℝ≥0` to reflect the rel distances?
Here, `S` can be empty. Maybe add a condition for every S non-empty, then blah
-/
noncomputable def generalProximityGap (P : Finset (ι → α)) (C : Finset (Finset (ι → α)))
 (Δ : (ι → α) → (ι → α) → ℕ) (δ ε : ℝ≥0) (S : Finset (ι → α)) (h' : S ∈ C) (h : S.Nonempty)
  : Prop :=
  (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} = 1
  ∨ (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} ≤ ε


-- noncomputable def setOfSubmodules [Field F] : Set (Submodule F (ι → F)) :=
--{A | ∃ B : Submodule F (ι → F), A = B}
-- Set.univ


lemma setOfSubmodules_nonempty :
  {A | ∃ B : Submodule F (ι → F), A = B}.Nonempty := by simp only [exists_eq', Set.setOf_true,
    Set.univ_nonempty]

lemma setOfSubmodules_finite [Fintype F] [Fintype ι] :
  {A | ∃ B : Submodule F (ι → F), A = B}.Finite := by
  simp only [exists_eq', Set.setOf_true]
  exact Set.finite_univ

-- Fintype.ofFinite

#print AffineSubspace

-- noncomputable def setOfAffineSubspaces [Field F] : Set (AffineSubspace F (ι → F)) :=
-- {A | ∃ B : AffineSubspace F (ι → F), A = B}


lemma setOfAffineSubspaces_nonempty :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Nonempty := by simp only [exists_eq', Set.setOf_true,
    Set.univ_nonempty]

lemma setOfAffineSubspaces_finite [Fintype F] [Fintype ι] :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Finite := by
  simp only [exists_eq', Set.setOf_true]
  exact Set.finite_univ

noncomputable def proximityParams [Fintype F] [Fintype ι] (δ : ℝ≥0) (deg : ℕ)
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
Theorem 1.4 (Main Theorem — Correlated agreement over lines) in Proximity Gaps
-/
theorem correlatedAgreement_lines [Fintype ι] [Nonempty ι] [Field F] [Fintype F]
(u : Fin 2 → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype F).toOuterMeasure
    {z | Code.relHammingDistToCode (u 1 + z • u 2) (ReedSolomon.code domain deg) ≤ δ}
      > proximityParams δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/--
Let `u := {u_1, ..., u_l}` be a collection of vectors in `F^ι`. The parameterised curve of degree
`l` generated by `u` is the set of linear combinations of the form `{∑ i ∈ l r ^ i • u_i | r ∈ F}`.
-/
def parametrisedCurve {l : ℕ} (u : Fin l → ι → F) : Set (ι → F) :=
  {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}

/--
A parametrised curve over a finite field.
-/
def parametrisedCurve' [Fintype ι] [Field F] [Fintype F] {l : ℕ} (u : Fin l → ι → F) :
Finset (ι → F) := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}


instance [Fintype ι] [Field F] [Fintype F] [Nonempty F] {l : ℕ} :
  ∀ u : Fin l → ι → F, Nonempty {x // x ∈ parametrisedCurve' u } := by
  intro u
  unfold parametrisedCurve'
  simp only [mem_filter, mem_univ, true_and, nonempty_subtype]
  obtain ⟨r⟩ := ‹Nonempty F›
  use ∑ i : Fin l, r ^ (i : ℕ) • u i, r


/--
Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in Proximity Gaps
-/
theorem correlatedAgreement_affine_curves [Fintype ι] [Nonempty ι] [Field F] [Fintype F]
[DecidableEq F]
{l : ℕ} (u : Fin l → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype (parametrisedCurve' u)).toOuterMeasure
    {y | Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}
    > l*(proximityParams δ deg domain)):
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

-- #check Set.range
-- #check affineSpan
-- /--
-- Theorem 1.6 (Correlated agreement over affine spaces) in Proximity Gaps
-- -/
-- theorem correlatedAgreement_affine_spaces [Fintype ι] [Nonempty ι] [Field F] [Fintype F]
-- {l : ℕ} (u : Fin (l+1) → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
-- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
-- (hproximity : (PMF.uniformOfFintype (affineSpan F (Set.range u))).toOuterMeasure
--     {y | Code.relHammingDistToCode y (ReedSolomon.code domain deg) ≤ δ}
--     > proximityParams δ deg domain) :
--   correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry


instance {l : ℕ} [NeZero l] : Nonempty (Fin l) := inferInstance

instance {l : ℕ} [NeZero l] : Fintype (Fin l) := inferInstance

-- instance {l : ℕ} [NeZero l] :
--   Inhabited (Finset.univ : Finset (Fin l)) := inferInstance

#check Fintype.ofFinite

instance {α : Type} [Fintype α] [Nonempty α] :
  Nonempty (Finset.univ : Finset α) := by exact Nonempty.to_subtype (univ_nonempty_iff.mpr (by assumption))
  -- refine Nonempty.to_subtype ?_


  -- rw [← Finset.univ_nonempty_iff]
  -- apply Finset.univ_nonempty


  -- haveI := @Finset.univ_nonempty (Fin (l+1)) _ _
  -- exact this



  -- apply Nonempty.intro
  -- exact ⟨0 , by simp⟩

def thing {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Finset (ι → F) :=
  Finset.univ.image u

namespace thing

theorem thing₁ {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  (thing u).Nonempty := by simp [thing]

instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  Nonempty (thing u) := by
  have := thing₁ (u := u)
  simp only [nonempty_subtype]
  exact this

theorem thing₂ {α P V : Type*} [AddCommGroup V] [Ring α] [Module α V] {s : Set P} (h : Set.Nonempty s)
               [AddTorsor V P] : Nonempty ↥(@affineSpan α V P _ _ _ _ s) := by
  have := @affineSpan_nonempty α V P _ _ _ _ s
  unfold Set.Nonempty at this h
  simp
  symm at this
  apply this.1
  exact h

theorem thing₄ {α P V : Type*} [AddCommGroup V] [Fintype α] [Ring α] [Module α V] [Fintype P] {s : Finset P}
           [AddTorsor V P] : Finite ↥(@affineSpan α V P _ _ _ _ s) := by
  unfold affineSpan
  infer_instance

noncomputable def thing₃ {α P V : Type*} [Fintype α] [AddCommGroup V]
                                         [Ring α] [Module α V] [Fintype P] {s : Finset P}
           [AddTorsor V P] : Fintype ↥(@affineSpan α V P _ _ _ _ s) := by
  have := @thing₄ α P V _ _ _ _ _ s _
  apply Fintype.ofFinite

end thing

def X (n : ℕ) : Type := {x : ℕ // x < n}

def eq {n : ℕ} : X n ≃ Fin n := sorry

#check Fin.add_one_le_of_lt

instance {n : ℕ} : Preorder (X n) where
  le a b := eq a ≤ eq b
  le_refl := λ _ ↦ Fin.le_refl _
  le_trans := λ _ _ _ ↦ Fin.le_trans

instance {n : ℕ} : Add (X n) := Equiv.add eq

instance {n : ℕ} [NeZero n] {i : ℕ} : OfNat (X n) i where
  ofNat := eq.symm (Fin.ofNat' n i)

theorem abc {n : ℕ} {a b : X (n + 1)} (h : a < b) : a + 1 ≤ b := by
  unfold LE.le
  unfold_projs
  simp
  apply Fin.add_one_le_of_lt
  unfold LT.lt at h
  unfold_projs at h
  simp at h
  exact h.2

theorem correlatedAgreement_affine_spaces' [Fintype ι] [Field F] [Fintype F]
  [DecidableEq F] [AddTorsor F (ι → F)]
  {k : ℕ} [NeZero k] (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
  -- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
    (hproximity : PMF.toOuterMeasure
                    (@PMF.uniformOfFintype
                      (@affineSpan F F (ι → F) _ _ _ _ (thing u))
                      (@thing.thing₃ F (ι → F) F _ _ _ _ _ (thing u) _)
                      (@thing.thing₂ F (ι → F) F _ _ _ (thing u)
                                       (@thing.thing₁ F ι _ k _ _ u) _)) > sorry) : False := by sorry

end






-- instance {l : ℕ} : Nonempty (Fin (l+1)) := inferInstance

-- instance {l : ℕ} : Fintype (Fin (l+1)) := inferInstance

-- instance {l : ℕ} [NeZero l] :
--   Nonempty (Finset.univ : Finset (Fin l)) := inferInstance


--   rw [← Finset.univ_nonempty_iff]
--   apply Finset.univ_nonempty


--   haveI := @Finset.univ_nonempty (Fin (l+1)) _ _
--   exact this



--   apply Nonempty.intro
--   exact ⟨0 , by simp⟩



-- theorem correlatedAgreement_affine_spaces' [Fintype ι] [Field F] [Fintype F]
-- [DecidableEq F]
-- {l : ℕ} (u : Fin (l+1) → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
-- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
-- (hproximity : (PMF.uniformOfFintype (affineSpan F (Finset.univ.image u))).toOuterMeasure
--     sorry
--     > proximityParams δ deg domain) :
--   correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry


-- --- { y : affineSpan F (Finset.univ.image u) |
-- -- Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}


-- #check Set.range
-- #check affineSpan
-- /--
-- Theorem 1.6 (Correlated agreement over affine spaces) in Proximity Gaps
-- --- how do I represent `u` as a set?
-- -/
-- theorem correlatedAgreement_affine_spaces'' [Fintype ι] [Nonempty ι] [Field F] [Fintype F]
-- {l : ℕ} (u : Fin (l+1) → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
-- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
-- (hproximity : (PMF.uniformOfFintype (affineSpan F (Set.range u))).toOuterMeasure
--     {y | Code.relHammingDistToCode y (ReedSolomon.code domain deg) ≤ δ}
--     > proximityParams δ deg domain) :
--   correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry



-- instance {l : ℕ} [NeZero l] : Nonempty (Fin l) := inferInstance

-- instance {l : ℕ} [NeZero l] : Fintype (Fin l) := inferInstance

-- -- instance {l : ℕ} [NeZero l] :
-- --   Inhabited (Finset.univ : Finset (Fin l)) := inferInstance

-- #check Fintype.ofFinite

-- instance {α : Type} [Fintype α] [Nonempty α] :
--   Nonempty (Finset.univ : Finset α) := by exact Nonempty.to_subtype (univ_nonempty_iff.mpr (by assumption))
--   -- refine Nonempty.to_subtype ?_


--   -- rw [← Finset.univ_nonempty_iff]
--   -- apply Finset.univ_nonempty


--   -- haveI := @Finset.univ_nonempty (Fin (l+1)) _ _
--   -- exact this



--   -- apply Nonempty.intro
--   -- exact ⟨0 , by simp⟩

-- def thing {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Finset (ι → F) :=
--   Finset.univ.image u

-- namespace thing

-- theorem thing₁ {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
--   (thing u).Nonempty := by simp [thing]

-- instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
--   Nonempty (thing u) := by
--   have := thing₁ (u := u)
--   simp only [nonempty_subtype]
--   exact this

-- lemma finite_filter_exists {α : Type*} {s : Finset α} {P : α → α → Prop} :
--   Finite {x : α | ∃ i ∈ ↑s, P x i} := by sorry

-- theorem thing₂ {α P V : Type*} [AddCommGroup V] [Ring α] [Module α V] {s : Set P} (h : Set.Nonempty s)
--                [AddTorsor V P] : Nonempty ↥(@affineSpan α V P _ _ _ _ s) := by
--   have := @affineSpan_nonempty α V P _ _ _ _ s
--   unfold Set.Nonempty at this h
--   simp
--   symm at this
--   apply this.1
--   exact h

-- theorem thing₄ {α P V : Type*} [AddCommGroup V] [Fintype α] [Ring α] [Module α V] [Module.Finite α V] {s : Finset P}
--            [AddTorsor V P] : Finite ↥(@affineSpan α V P _ _ _ _ s) := by
--   unfold affineSpan
--   suffices Finite (spanPoints α s.toSet) by aesop
--   unfold spanPoints
--   exact finite_filter_exists


--   -- rw [@Set.finite_coe_iff]
--   -- simp only [mem_coe]



--   -- suffices Finite ↑{p | True} by done


--   --   done
--   -- -- obtain ⟨n, s, h⟩ := @Module.Finite.exists_fin α V _ _ _ _


-- noncomputable def thing₃ {α P V : Type*} [Fintype α] [AddCommGroup V] [Ring α] [Module α V] {s : Finset P}
--            [AddTorsor V P] : Fintype ↥(@affineSpan α V P _ _ _ _ s) := by
--   have := @thing₄ α P V _ _ _ _ s _
--   apply Fintype.ofFinite

-- end thing

-- theorem correlatedAgreement_affine_spaces' [Fintype ι] [Field F] [Fintype F]
--   [DecidableEq F] [AddTorsor F (ι → F)]
--   {k : ℕ} [NeZero k] (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
--   -- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
--     (hproximity : PMF.toOuterMeasure
--                     (@PMF.uniformOfFintype
--                       (@affineSpan F F (ι → F) _ _ _ _ (thing u))
--                       (@thing.thing₃ F (ι → F) F _ _ _ _ (thing u) _)
--                       (@thing.thing₂ F (ι → F) F _ _ _ (thing u)
--                                        (@thing.thing₁ F ι _ k _ _ u) _)) > sorry) : False := by sorry

--   -- (hproximity : (@PMF.uniformOfFintype (@affineSpan F F
--   --                                         (ι → F) _ _ _ {vsub := sorry, vsub_vadd' := sorry, vadd_vsub' := sorry}
--   --                                         (Finset.univ.image u))
--   --                                         (let x : AffineSubspace F (ι → F) := affineSpan F ↑(image u univ)
--   --                                          let y : Set _ := SetLike.coe x
--   --                                          by have : y = ↑x := by aesop
--   --                                             simp [x] at this
--   --                                             have : Finite y := by
--   --                                               rw [this]
--   --                                               exact Subtype.finite
--   --                                             simp [y, x] at this
--   --                                             have := Fintype.ofFinite ↑(spanPoints F (Set.range u))
--   --                                             simp
--   --                                             simp_rw [←coe_affineSpan] at this
--   --                                             convert this
--   --                                             ext x
--   --                                             simp
--   --                                             refine ⟨λ h ↦ ?p₁, λ h ↦ ?p₂⟩
--   --                                             sorry
--   --                                             sorry
--   --                                         ) (by have := Set.Nonempty.affineSpan
--   --                                               simp
--   --                                               use 0
--   --                                               sorry)).toOuterMeasure
--   --     sorry
--   --     > 42.) : False := by
--   sorry
--   -- correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry


-- --- { y : affineSpan F (Finset.univ.image u) |
-- -- Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}

-- -- end

-- -- instance {l : ℕ} [NeZero l] : Nonempty (Fin l) := inferInstance

-- -- instance {l : ℕ} [NeZero l] : Fintype (Fin l) := inferInstance

-- -- -- instance {l : ℕ} [NeZero l] :
-- -- --   Inhabited (Finset.univ : Finset (Fin l)) := inferInstance

-- -- #check Fintype.ofFinite

-- -- instance {α : Type} [Fintype α] [Nonempty α] :
-- --   Nonempty (Finset.univ : Finset α) := by exact Nonempty.to_subtype (univ_nonempty_iff.mpr (by assumption))
-- --   -- refine Nonempty.to_subtype ?_


-- --   -- rw [← Finset.univ_nonempty_iff]
-- --   -- apply Finset.univ_nonempty


-- --   -- haveI := @Finset.univ_nonempty (Fin (l+1)) _ _
-- --   -- exact this



-- --   -- apply Nonempty.intro
-- --   -- exact ⟨0 , by simp⟩



-- -- theorem correlatedAgreement_affine_spaces' [Fintype ι] [Field F] [Fintype F]
-- -- [DecidableEq F]
-- -- {l : ℕ} [NeZero l] (u : Fin l → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
-- -- -- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
-- --   (hproximity : (@PMF.uniformOfFintype (@affineSpan F F
-- --                                           (ι → F) _ _ _ {vsub := sorry, vsub_vadd' := sorry, vadd_vsub' := sorry}
-- --                                           (Finset.univ.image u))
-- --                                           (let x : AffineSubspace F (ι → F) := affineSpan F ↑(image u univ)
-- --                                            let y : Set _ := SetLike.coe x
-- --                                            by have : y = ↑x := by aesop
-- --                                               simp [x] at this
-- --                                               have : Finite y := by
-- --                                                 rw [this]
-- --                                                 exact Subtype.finite
-- --                                               simp [y, x] at this
-- --                                               have := Fintype.ofFinite ↑(spanPoints F (Set.range u))
-- --                                               simp
-- --                                               simp_rw [←coe_affineSpan] at this
-- --                                               convert this
-- --                                               ext x
-- --                                               simp
-- --                                               refine ⟨λ h ↦ ?p₁, λ h ↦ ?p₂⟩
-- --                                               sorry
-- --                                               sorry
-- --                                           ) (by have := Set.Nonempty.affineSpan
-- --                                                 simp
-- --                                                 use 0
-- --                                                 sorry)).toOuterMeasure
-- --       sorry
-- --       > 42.) : False := by
-- --   sorry
-- --   -- correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry


-- -- --- { y : affineSpan F (Finset.univ.image u) |
-- -- -- Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}

-- -- end

-- end
