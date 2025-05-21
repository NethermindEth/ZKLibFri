import Init.Data.List.FinRange
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul 
import Mathlib.Data.Matrix.Reflection

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.ElocPoly
import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries
import ArkLib.Data.CodingTheory.BerlekampWelch.Existence
import ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import ArkLib.Data.CodingTheory.BerlekampWelch.ToMathlib
import ArkLib.Data.CodingTheory.HammingDistance.Lemmas
import ArkLib.Data.Fin.Basic

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}
         {e k : ℕ} {ωs f : Polynomial F}

open Polynomial

section

variable [DecidableEq F]

noncomputable def decoder (e k : ℕ) [NeZero n] (ωs f : Fin n → F) : Option (Polynomial F) :=
  if ‖f‖₀ ≤ e
  then some 0 
  else 
    let x := linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    match x with 
    | none => none 
    | some x => 
      let E := solution_to_E e k x
      let Q := solution_to_Q e k x 
      if Q % E = 0 then 
        let p := Q / E 
        if Δ₀(f, p.eval ∘ ωs) ≤ e then 
          some p
        else 
          none
      else
        none

lemma hammingDist_le_of_decoder_eq_some [NeZero n] {ωs f : Fin n → F} 
  (h : decoder e k ωs f = some p) : Δ₀(f, p.eval ∘ ωs) ≤ e :=
  by aesop (add simp decoder)

lemma decoder_eq_some {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) 
  : decoder e k ωs f = some p := by 
  simp only [decoder]
  split_ifs with hif
  · suffices p = 0 from Option.some_inj.2 this.symm
    refine an_implication_of_min_dist h_deg hn h_inj (lt_of_le_of_lt ?p₁ he)
    transitivity ‖f‖₀ + Δ₀(f, p.eval ∘ ωs)
    · convert hammingDist_triangle 0 f (p.eval ∘ ωs) using 1 <;> simp
    · omega
  · rcases hlinsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    · simp only [reduceCtorEq]; exact linsolve_always_some_berlekamp_welch h_deg h_dist hlinsolve
    · by_cases hp : p = 0 
      · have : ‖f‖₀ ≤ e := by aesop
        omega
      · have h_cond := linsolve_to_BerlekampWelch_condition hlinsolve
        have h :=
          Q'_div_E'_eq_p
            h_deg he hn h_dist h_inj
            (solution_to_Q_ne_0 (not_le.1 hif)
                                (BerlekampWelchCondition_iff_Solution.2 h_cond) h_inj) hp h_cond
        simp_all

lemma not_exists_of_decoder_eq_none {e k : ℕ} [NeZero n] {ωs f : Fin n → F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_none : decoder e k ωs f = none)
  : ¬∃p : F[X], Δ₀(f, p.eval ∘ ωs) ≤ e ∧ p.natDegree < k := by 
  intro contr
  aesop (add safe forward (decoder_eq_some))

end

end BerlekampWelch
