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
import ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries
import ArkLib.Data.CodingTheory.BerlekampWelch.ToMathlib
import ArkLib.Data.CodingTheory.HammingDistance.Lemmas

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {n : ℕ} {p : Polynomial F}
variable [DecidableEq F]

open ElocPoly
open Polynomial

noncomputable def E {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  X ^ (e - (Δ₀(f, p.eval ∘ ωs) : ℕ)) * ElocPolyF (ωs := ωs) f p

lemma E_natDegree 
  {e : ℕ} 
  {ωs f : Fin n → F} 
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (E (ωs := ωs) f p e).natDegree = e  
  := by
  unfold E
  rw [natDegree_mul (by aesop) (by aesop)]
  simp only [natDegree_pow, natDegree_X, mul_one, elocPolyF_deg] 
  rw [Nat.sub_add_cancel (by omega)]

lemma E_ne_0 {e : ℕ} {ωs f : Fin n → F} : (E ωs f p e) ≠ 0 := by
  unfold E
  intro contr
  rw [mul_eq_zero] at contr
  rcases contr with contr | contr
    <;> try simp at contr 

lemma errors_are_roots_of_E {i : Fin n} {e} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (E ωs f p e).eval (ωs i) = 0  := by
  unfold E 
  aesop 
    (erase simp [BerlekampWelch.elocPolyF_eq_elocPoly']) 
    (add simp [BerlekampWelch.errors_are_roots_of_elocPolyF])

@[simp]
lemma E_leading_coeff {e} {ωs f : Fin n → F}
  : (E ωs f p e).leadingCoeff = 1 := by
  simp [E]

lemma E_leading_coeff' {e} {ωs f : Fin n → F}
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) 
  : (E ωs f p e).coeff e = 1 := by
  conv =>
    lhs 
    congr 
    rfl 
    rw [←E_natDegree h_dist]
    rfl
  rw [Polynomial.coeff_natDegree]
  simp

noncomputable def Q {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  p * (E ωs f p e)

lemma Q_natDegree 
  {e : ℕ} {ωs f : Fin n → F}
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (Q ωs f p e).natDegree ≤ e + p.natDegree := by
  unfold Q
  by_cases h0 : p = 0   
  · aesop
  · aesop 
      (add simp [ natDegree_mul, E_ne_0, E_natDegree]) 
      (add safe (by omega))

lemma Q_ne_0 
  {e : ℕ} {ωs f : Fin n → F}
  (hne : p ≠ 0)
  : Q ωs f p e ≠ 0 := by
  unfold Q 
  aesop 
    (add simp [E_ne_0])

lemma E_and_Q_BerlekampWelch_condition {e k : ℕ} {ωs f : Fin n → F}
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) 
  : BerlekampWelchCondition e k ωs f (E ωs f p e) (Q ωs f p e) := by
  exact ⟨
  by {
    intro i
    unfold Q E
    by_cases hi : f i = p.eval (ωs i)
    · aesop 
    · aesop 
        (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
        (add simp [BerlekampWelch.errors_are_roots_of_elocPolyF])
  },
  by simp [E_natDegree h_dist],
  by simp [E_leading_coeff' h_dist],
  by aesop 
    (add safe forward (Q_natDegree h_dist))
    (add safe (by omega))
  ⟩

lemma Q'_div_E'_eq_p {e k : ℕ}
  [NeZero n]
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hp_deg: p.natDegree < k)
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (h_Q' : Q' ≠ 0)
  (hp : p ≠ 0)
  (h_cond: BerlekampWelchCondition e k ωs f E' Q')
  : E' ∣ Q' ∧ Q' / E' = p  := by
  have h_eq := E_and_Q_unique he hk_n (Q_ne_0 hp) h_Q' h_diff 
    (E_and_Q_BerlekampWelch_condition hp_deg h_ham)
    h_cond
  apply And.intro
  · simp [Q] at h_eq
    rw [←mul_assoc, mul_comm _ (E _ _ _ _)] at h_eq 
    aesop (add simp E_ne_0)
  · simp [Q] at h_eq
    rw [←mul_assoc, mul_comm _ (E _ _ _ _)] at h_eq 
    aesop (add simp E_ne_0)

lemma linsolve_always_some_berlekamp_welch 
  {e k : ℕ}
  [NeZero n]
  {ωs f : Fin n → F}
  (hp_deg: p.natDegree < k)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) ≠ none := by
  by_cases hk : 1 ≤ k
  · intro contr
    apply linsolve_none contr
    exists E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)
    rw [BerlekampWelchCondition_to_Solution hk (E_and_Q_BerlekampWelch_condition hp_deg h_ham)]
  · simp at hk
    simp [hk] at hp_deg

end BerlekampWelch
