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
  if Δ₀(f, 0) ≤ e 
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

lemma decoder_some [NeZero n] {ωs f : Fin n → F} 
  (h : decoder e k ωs f = some p) 
  : Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [decoder] at h
  split_ifs at h with hif
  · aesop 
  · generalize h_linsolve:
     linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = solution 
    rcases solution with _ | solution <;> simp [h_linsolve] at h
    aesop 
      (add safe forward (linsolve_to_BerlekampWelch_condition h_linsolve))

lemma decoder_some' {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, (fun a => Polynomial.eval a p) ∘ ωs) ≤ e) 
  : decoder e k ωs f = some p := by 
  simp only [decoder]
  split_ifs with hif
  · have h_dist : Δ₀((fun a ↦ eval a p) ∘ ωs, (0 : Fin n → F)) ≤ 2 * e
      := Nat.le_trans (hammingDist_triangle _ _ (y := f)) (by {
        rw [hammingDist_comm]
        omega
      })
    rw [an_implication_of_min_dist (p := p)]
      <;> aesop (add safe (by omega))
  · generalize hlinsolve 
      : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = solution 
    rcases solution with _ | x <;> simp 
    · apply linsolve_always_some_berlekamp_welch (n := n) (p := p) <;>
        aesop (add safe (by omega))
    · simp at hif
      have h_cond := linsolve_to_BerlekampWelch_condition hlinsolve
      by_cases hp : p = 0 
      · aesop 
          (add simp [hammingNorm, hammingDist])
          (add safe (by omega))
      · have h := Q'_div_E'_eq_p h_deg he hn h_dist h_inj
          (solution_to_Q_ne_0 (by aesop) (by 
            aesop (add simp [BerlekampWelchCondition_iff_Solution])
          ) h_inj) hp h_cond
        aesop 

lemma decoder_none {e k : ℕ} [NeZero n] {ωs f : Fin n → F} 
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_none : decoder e k ωs f = none)
  : ¬∃p, Δ₀(f, (fun a => Polynomial.eval a p) ∘ ωs) ≤ e ∧ p.natDegree < k := by 
  intro contr 
  aesop (add safe forward (decoder_some'))

end

end BerlekampWelch
