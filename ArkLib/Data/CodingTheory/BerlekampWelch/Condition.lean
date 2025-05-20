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
import ArkLib.Data.CodingTheory.BerlekampWelch.ToMathlib
import ArkLib.Data.CodingTheory.HammingDistance.Lemmas

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {n : ℕ} 

structure BerlekampWelchCondition (e k : ℕ) (ωs f : Fin n → F) (E Q : Polynomial F): Prop where
  cond: ∀ i : Fin n, Q.eval (ωs i) = (f i) * E.eval (ωs i) 
  E_natDegree : E.natDegree = e
  E_leadingCoeff : E.coeff e = 1 
  Q_natDegree : Q.natDegree ≤ e + k - 1  

def BerlekampWelchMatrix [NeZero n] 
  (e k : ℕ) 
  (ωs f : Fin n → F) : Matrix (Fin n) (Fin (2 * e + k)) F := 
  Matrix.of (fun i j => 
    let αᵢ := ωs i
    if ↑j < e then (f i * αᵢ^(↑j : ℕ)) else -αᵢ^(↑j - e))

def Rhs [NeZero n] (e : ℕ) (ωs f : Fin n → F) (i : Fin n) : F := 
  let αᵢ := ωs i
  (-(f i) * αᵢ^e)

def IsBerlekampWelchSolution [NeZero n] 
  (e k : ℕ) 
  (ωs f : Fin n → F)
  (v : Fin (2 * e + k) → F)
  : Prop 
  := Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v = (Rhs e ωs f)

lemma linsolve_is_berlekamp_welch_solution [NeZero n]
  {e k : ℕ}
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_linsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = some v)
  : IsBerlekampWelchSolution e k ωs f v := by
  simp [IsBerlekampWelchSolution, linsolve_some h_linsolve]

lemma is_berlekamp_welch_solution_ext [NeZero n]
  {e k : ℕ} 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h : ∀ i, (Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v) i 
    = (-(f i) * (ωs i)^e) )
  : IsBerlekampWelchSolution e k ωs f v := by
  aesop (add simp [IsBerlekampWelchSolution, Rhs])

noncomputable def E_and_Q_to_a_solution (e : ℕ) (E Q : Polynomial F) (i : Fin n) : F :=
  match (E, Q) with
  | (⟨⟨_, f, _⟩⟩, ⟨⟨_, g, _⟩⟩) => if i < e then f i else g (i - e)

@[simp]
lemma E_and_Q_to_a_solution_coeff 
  {e : ℕ} 
  {E Q : Polynomial F} 
  {i : Fin n}
  : (E_and_Q_to_a_solution e E Q) i = if i < e then E.coeff i else Q.coeff (i - e) := by
  rcases E with ⟨⟨_, f, _⟩⟩
  rcases Q with ⟨⟨_, g, _⟩⟩
  simp [E_and_Q_to_a_solution]

section 

lemma BerlekampWelchCondition_to_Solution {e k : ℕ} [NeZero n]
  {ωs f : Fin n → F} {E Q : Polynomial F} 
  (hk_or_e : 1 ≤ k ∨ 1 ≤ e)
  (h : BerlekampWelchCondition e k ωs f E Q)
  : IsBerlekampWelchSolution e k ωs f (E_and_Q_to_a_solution e E Q) := by
  rcases h with ⟨h_cond, h_E_deg, h_E_coeff, h_Q_deg⟩
  apply is_berlekamp_welch_solution_ext
  intro i
  rw [←Matrix.mulVecᵣ_eq]
  simp [Matrix.mulVecᵣ, dotProduct]
  rw [Finset.sum_ite]
  simp [BerlekampWelchMatrix]
  let seg_e := insert ⟨e, by omega⟩ {x : Fin (2 * e + k) | ↑x < e} 
  have hhh : ∑ i_1 ∈ {x : Fin (2 * e + k) | ↑x < e}, ωs i ^ (↑i_1 : ℕ) * E.coeff ↑i_1 = 
        ∑ i_1 ∈ seg_e, ωs i ^ (↑i_1 : ℕ) * E.coeff ↑i_1 - 
                ωs i ^ ↑e * E.coeff ↑e := by simp [seg_e]
  have hhhr : ∑ x ∈ {x: Fin (2 * e + k) | ↑x < e + k }, ωs i ^ (↑x : ℕ) * Q.coeff ↑x 
    =∑ x ∈ Finset.range (e + k), ωs i ^ x * Q.coeff x := by
      apply Finset.sum_bij (i := fun a ha => a.val)
        <;> try aesop (config := {warnOnNonterminal := false}) (add safe (by omega))
      exists ⟨b, by omega⟩
      exists ⟨b, by omega⟩
  conv =>
    lhs
    congr 
    · rw [Finset.sum_ite_of_true (by aesop),
        Finset.sum_equiv (t := {x : Fin (2 * e + k) | ↑x < e })
          (g := fun j => f i * (ωs i ^ (↑j : ℕ) * E.coeff ↑j))
          (Equiv.refl (Fin (2 * e + k))) 
          (by aesop)
          (by {
            intro j hj
            rw [mul_assoc]
            rfl
          }),
          ←Finset.mul_sum _ _ (f i),
          hhh,
          Finset.sum_bij (t := Finset.range e.succ)
            (i := fun a ha => a.val)
            (hi := by 
              simp [seg_e]; omega
            )
            (i_inj := by aesop (add simp seg_e))
            (i_surj := by {
              simp [seg_e]
              intro b hb 
              rcases hb with _ | hb <;> try simp 
              right
              exists ⟨b, by {
                apply Nat.lt_trans (Nat.lt_of_succ_le hb)
                omega
              }⟩
            })
            (h := by {
              intro a ha
              rcases a with ⟨a, h_lt⟩
              simp
              rfl 
            }), 
          ←Polynomial.sum_eq_of_subset _ (by simp) (by {
             intro x hx
             simp 
             simp at hx 
             rw [←Polynomial.ite_le_natDegree_coeff _ _ inferInstance] at hx 
             split_ifs at hx with hif 
             rw [h_E_deg] at hif 
             omega 
             tauto 
          }),
          polynomial_sum_ext 
            (g := fun x a => a * ωs i ^ x) 
            (by aesop 
              (add safe 
                (by ring_nf))),
          ←Polynomial.eval_eq_sum] 
    rfl
  · {
    rw [Finset.sum_ite_of_false (by simp)]
    rw [Finset.sum_bij (g := fun x => -(ωs i ^ (↑x : ℕ) * Q.coeff ↑x)) 
      (t := { x : Fin (2 * e + k)  | x < e + k }) (by {
      intro a ha 
      exact (⟨↑a - e, by omega⟩ : Fin (2 * e + k))
    }) (by {
      rintro ⟨a, ha⟩
      simp
      omega
    }) (by simp; omega
    ) (by {
      rintro ⟨b, hb⟩ hh
      exists ⟨b + e, by 
        simp at hh
        omega
      ⟩
      simp
    }) (by {
     rintro ⟨a, hfin⟩ ha
     simp at ha 
     simp only [Fin.val]
    })]
    rw [Finset.sum_neg_distrib]
    rw [hhhr]
    rw [←Polynomial.sum_eq_of_subset (p := Q) (fun j x => ωs i ^ j * x) (by simp) (by {
        intro x hx 
        simp 
        simp at hx 
        rw [←Polynomial.ite_le_natDegree_coeff _ _ inferInstance ] at hx 
        split_ifs at hx with hif
        apply Nat.lt_of_lt_of_le hif
        trans 
        apply Nat.add_le_add_left h_Q_deg
        omega
        aesop 
     })]
    rw [polynomial_sum_ext 
            (g := fun x a => a * ωs i ^ x) 
            (by {
              intro j x 
              simp 
              ring
            })]
    rw [←Polynomial.eval_eq_sum]
    rw [mul_sub]
    rw [←h_cond, add_comm]
    rw [←add_sub_assoc]
    rw [add_comm (b := Polynomial.eval _ _)]
    rw [add_neg_cancel]
    simp [zero_sub, h_E_coeff]
  }

open Fin
open Polynomial

variable [DecidableEq F]

def solution_to_E (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨insert e ((Finset.range e).filter (fun x => liftF v x ≠ 0)), 
    fun i => if i = e then 1 else if i < e then liftF v i else 0, by 
      aesop (add safe forward liftF_ne_0)
    ⟩⟩

@[simp]
lemma solution_to_E_coeff {e k : ℕ} {v : Fin (2 * e + k) → F} {i : ℕ}:
  (solution_to_E e k v).coeff i = if i = e then 1 else if i < e then liftF v i else 0 := rfl

@[simp]
lemma solution_to_E_natDegree {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_E e k v).natDegree = e := by
  simp [solution_to_E, Polynomial.natDegree, Polynomial.degree]
  rw [sup_eq_left.2 ] <;> try simp
  omega

@[simp]
lemma solution_to_E_0 {k : ℕ} {v : Fin (2 * 0 + k) → F} :
  solution_to_E 0 k v = C (1 : F) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_C]
  rcases n with _ | n <;> try simp 

lemma solution_to_E_ne_0 {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_E e k v) ≠ 0 := by
  by_cases he : e = 0 
  · subst he
    simp
  · have h_deg : (solution_to_E e k v).natDegree > 0 := by 
      aesop (add safe (by omega))
    intro contr
    rw [contr] at h_deg 
    simp at h_deg 

def solution_to_Q (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨(Finset.range (e + k)).filter (fun x => liftF v (e + x) ≠ 0), 
    fun i => if i < e + k then liftF v (e + i) else 0, by {
      aesop (add safe (by omega))
    }⟩⟩

@[simp]
lemma solution_to_Q_coeff {e k : ℕ} {v : Fin (2 * e + k) → F} {i : ℕ}:
  (solution_to_Q e k v).coeff i = if i < e + k then liftF v (e + i) else 0 := rfl

@[simp]
lemma solution_to_Q_natDegree {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_Q e k v).natDegree ≤ e + k - 1 := by
  simp [solution_to_Q, Polynomial.natDegree, Polynomial.degree]
  rw [WithBot.unbotD_le_iff] <;>
  aesop (add safe [(by omega)])

@[simp]
lemma solution_to_E_and_Q_E_and_Q_to_a_solution 
  {e k : ℕ} {v : Fin (2 * e + k) → F} 
  :
  E_and_Q_to_a_solution e (solution_to_E e k v) (solution_to_Q e k v) 
  = 
  v := by
  ext i
  simp [solution_to_E, solution_to_Q]
  split_ifs with hif₁ hif₂ <;> 
    aesop 
      (add simp [liftF])
      (add safe (by omega))

lemma BerlekampWelchCondition_to_Solution' {e k : ℕ} [NeZero n]
  {ωs f : Fin n → F} {v : Fin (2 * e + k) → F} 
  (h : BerlekampWelchCondition e k ωs f (solution_to_E e k v) (solution_to_Q e k v))
  : IsBerlekampWelchSolution e k ωs f v := by
  by_cases hk : 1 ≤ k
  · rw [←solution_to_E_and_Q_E_and_Q_to_a_solution (v := v)]
    exact BerlekampWelchCondition_to_Solution (by aesop) h
  · simp at hk 
    subst hk
    by_cases he: e = 0
    · subst he 
      ext i
      simp [IsBerlekampWelchSolution, BerlekampWelchMatrix, Rhs]
      rcases h with ⟨h1, h2, h3, h4⟩
      specialize h1 i 
      simp at h1 
      aesop 
        (add simp [solution_to_Q, eval_eq_sum, Polynomial.sum])
    · rw [←solution_to_E_and_Q_E_and_Q_to_a_solution (v := v)]
      exact BerlekampWelchCondition_to_Solution (by omega) h
 
lemma solution_to_BerlekampWelch_condition₀ {e : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + 0) → F}
  (h_sol : IsBerlekampWelchSolution e 0 ωs f v)
  : BerlekampWelchCondition e 0 ωs f (solution_to_E e 0 v) (solution_to_Q e 0 v) := by
  exact ⟨
    by {
    by_cases he : e = 0 
    subst he 
    intro i
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
    simp [solution_to_E, solution_to_Q, Polynomial.sum]
    simp [IsBerlekampWelchSolution] at h_sol 
    have h_sol : (0 : Fin n → F) i = Rhs 0 ωs f i := by rw [h_sol]
    simp [Rhs] at h_sol 
    rw [h_sol]
    intro i
    symm
    conv =>
      lhs
      rw [Polynomial.eval_eq_sum_range]
      rfl
    rw [Finset.range_succ]
    rw [Finset.sum_insert (by aesop)]
    simp
    rw [Finset.sum_ite_of_false (by aesop)]
    rw [Finset.sum_ite_of_true (by aesop)]
    rw [Polynomial.eval_eq_sum_range' (n := e + 0) 
          (Nat.lt_of_le_of_lt solution_to_Q_natDegree (by omega))]
    simp 
    rw [Finset.sum_ite_of_true (by aesop)]
    simp [IsBerlekampWelchSolution] at h_sol 
    have h_sol : (BerlekampWelchMatrix e 0 ωs f).mulVec v i = Rhs e ωs f i := by
      rw [h_sol]
    simp [BerlekampWelchMatrix, Rhs, Matrix.mulVec, dotProduct] at h_sol 
    have h_aux {a b : F} : a = -b → -a = b := by aesop
    have h_sol := h_aux h_sol 
    rw [mul_add, ←h_sol]
    rw [Finset.sum_ite]
    conv =>
      congr 
      congr 
      congr 
      congr
      rw [Finset.sum_bij
        (t := Finset.range e)
        (g := fun a => f i * (liftF v a * ωs i ^ a))
        (by {
          rintro ⟨a, hfin⟩ ha
          exact a
        })
        (by {
          rintro ⟨a, hfin⟩ ha 
          simp
          simp at ha 
          exact ha
        })
        (by aesop)
        (by {
          intro b hb
          simp 
          exists ⟨b, by {
            aesop (add safe (by omega))
          }⟩
          simp 
          aesop
        })
        (by {
          rintro ⟨a, hfin⟩ ha
          simp [liftF, hfin ]
          ring
        })]
      rfl
      rfl 
      rfl
      rfl
    rw [Finset.mul_sum]
    rw [neg_add, add_comm]
    rw [←add_assoc]
    rw [add_neg_cancel]
    simp 
    apply Finset.sum_bij (by {
      intro a ha 
      exact a.val - e
    })
    · rintro ⟨a, ha⟩
      simp
      omega 
    · aesop (add safe (by omega))
    · intro b hb 
      exists ⟨b + e, by aesop (add safe (by omega))⟩
      aesop
    · rintro ⟨a, hfin⟩ ha 
      simp 
      simp at ha
      simp [liftF]
      aesop (add safe (by ring))
    },
    by simp,
    by simp,
    by {
      apply solution_to_Q_natDegree
    }⟩

lemma solution_to_BerlekampWelch_condition {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  : BerlekampWelchCondition e k ωs f (solution_to_E e k v) (solution_to_Q e k v) := by
  by_cases hk : 1 ≤ k 
  · exact ⟨by {
    intro i
    symm
    conv =>
      lhs
      rw [Polynomial.eval_eq_sum_range]
      rfl
    rw [Finset.range_succ]
    rw [Finset.sum_insert (by aesop)]
    simp
    rw [Finset.sum_ite_of_false (by aesop)]
    rw [Finset.sum_ite_of_true (by aesop)]
    rw [Polynomial.eval_eq_sum_range' (n := e + k) 
          (Nat.lt_of_le_of_lt solution_to_Q_natDegree (by omega))]
    simp 
    rw [Finset.sum_ite_of_true (by aesop)]
    simp [IsBerlekampWelchSolution] at h_sol 
    have h_sol : (BerlekampWelchMatrix e k ωs f).mulVec v i = Rhs e ωs f i := by
      rw [h_sol]
    simp [BerlekampWelchMatrix, Rhs, Matrix.mulVec, dotProduct] at h_sol 
    have h_aux {a b : F} : a = -b → -a = b := by aesop
    have h_sol := h_aux h_sol 
    rw [mul_add, ←h_sol]
    rw [Finset.sum_ite]
    conv =>
      congr 
      congr 
      congr 
      congr
      rw [Finset.sum_bij
        (t := Finset.range e)
        (g := fun a => f i * (liftF v a * ωs i ^ a))
        (by {
          rintro ⟨a, hfin⟩ ha
          exact a
        })
        (by {
          rintro ⟨a, hfin⟩ ha 
          simp
          simp at ha 
          exact ha
        })
        (by aesop)
        (by {
          intro b hb
          simp 
          exists ⟨b, by {
            aesop (add safe (by omega))
          }⟩
          simp 
          aesop
        })
        (by {
          rintro ⟨a, hfin⟩ ha
          simp [liftF, hfin ]
          ring
        })]
      rfl
      rfl 
      rfl
      rfl
    rw [Finset.mul_sum]
    rw [neg_add, add_comm]
    rw [←add_assoc]
    rw [add_neg_cancel]
    simp 
    apply Finset.sum_bij (by {
      intro a ha 
      exact a.val - e
    })
    · rintro ⟨a, ha⟩
      simp
      omega 
    · aesop (add safe (by omega))
    · intro b hb 
      exists ⟨b + e, by aesop (add safe (by omega))⟩
      aesop
    · rintro ⟨a, hfin⟩ ha 
      simp 
      simp at ha
      simp [liftF]
      aesop (add safe (by ring))
  }, 
  by simp,
  by simp,
  by simp⟩
  · simp at hk 
    subst hk
    apply solution_to_BerlekampWelch_condition₀ h_sol

lemma linsolve_to_BerlekampWelch_condition {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_sol : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = some v)
  : BerlekampWelchCondition e k ωs f (solution_to_E e k v) (solution_to_Q e k v) := 
  solution_to_BerlekampWelch_condition (linsolve_is_berlekamp_welch_solution h_sol)

end


lemma BerlekampWelch_E_ne_0 {e k : ℕ}
  {ωs f : Fin n → F}
  {E Q : Polynomial F}
  (h_cond : BerlekampWelchCondition e k ωs f E Q)
  : E ≠ 0 := by
  have h_deg := h_cond.E_natDegree
  have h_leadCoeff := h_cond.E_leadingCoeff
  aesop
 
section 

open Polynomial 

variable [DecidableEq F]

lemma BerlekampWelch_Q_ne_0 {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {E Q : Polynomial F}  
  (h_bw : BerlekampWelchCondition e k ωs f E Q) 
  (h_dist : e < Δ₀(f, 0))
  (h_inj : Function.Injective ωs)
  : Q ≠ 0 := by
  intro contr
  have h_cond := h_bw.cond
  simp [hammingDist] at *
  rw [contr] at h_cond 
  simp at h_cond
  have h_card := Polynomial.card_le_degree_of_subset_roots 
    (Z := Finset.image ωs ({i : Fin n | ¬ f i = 0} : Finset (Fin n))) (p := E)
    ( by {
      intro x hx
      simp at hx 
      rcases hx with ⟨i, ⟨hf, hi⟩⟩ 
      specialize (h_cond i)
      simp [BerlekampWelch_E_ne_0 h_bw]
      aesop 
    })
  simp at h_card 
  rw [Finset.card_image_of_injective _ h_inj, h_bw.E_natDegree] at h_card
  omega

lemma solution_to_Q_ne_0 {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_dist : e < Δ₀(f, 0))
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  (h_inj : Function.Injective ωs)
  : solution_to_Q e k v ≠ 0 := 
    BerlekampWelch_Q_ne_0 
      (solution_to_BerlekampWelch_condition h_sol) 
      h_dist
      h_inj

lemma E_and_Q_unique 
  [NeZero n]
  {e k : ℕ} 
  {E Q E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_Q : Q ≠ 0)
  (h_Q' : Q' ≠ 0)
  (h_inj : Function.Injective ωs)
  (h_bw₁ : BerlekampWelchCondition e k ωs f E Q)
  (h_bw₂ : BerlekampWelchCondition e k ωs f E' Q')
: E * Q' = E' * Q := by
  let R := E * Q' - E' * Q
  have hr_deg : R.natDegree ≤ 2 * e + k - 1 := by
    simp [R]
    apply Nat.le_trans (natDegree_add_le _ _)
    simp  [
      natDegree_mul 
        (BerlekampWelch_E_ne_0 h_bw₁) 
        h_Q',
      natDegree_neg,
      natDegree_mul 
        (BerlekampWelch_E_ne_0 h_bw₂)
        h_Q
      ]
    aesop 
      (add simp [Nat.max_le, h_bw₁.E_natDegree, h_bw₂.E_natDegree])
      (add safe forward (h_bw₁.Q_natDegree))
      (add safe forward (h_bw₂.Q_natDegree))
      (add safe (by omega))
  by_cases hr : R = 0 
  · rw [←add_zero (E' * Q)
       , ←hr]
    ring
  · let roots := Multiset.ofList <| List.map ωs  
        (List.finRange n)
    have hsub : (⟨roots, by 
        rw [Multiset.coe_nodup, List.nodup_map_iff h_inj]        
         ;
        aesop 
          (add simp [Multiset.coe_nodup])
          (add simp [List.Nodup, List.pairwise_iff_get])
      ⟩ : Finset F).val ⊆ R.roots := by
      {
        intro x hx
        aesop 
          (add simp [mem_roots, roots, R, h_bw₁.cond, h_bw₂.cond])
          (add safe (by ring))
      }
    have hcard := card_le_degree_of_subset_roots hsub
    by_cases hk : 1 ≤ k 
    · aesop (add safe (by omega))
    · simp at hk 
      by_cases he: e = 0
      · aesop
      · aesop (add safe (by omega))

end

end BerlekampWelch
