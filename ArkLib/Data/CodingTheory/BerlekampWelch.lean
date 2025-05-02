import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

import ArkLib.Data.CodingTheory.Basic

variable {F : Type} [Field F] [DecidableEq F]
         {n : ℕ}

open Polynomial

noncomputable def ElocPoly (n : ℕ) (ωs f : ℕ → F) (p : Polynomial F) : Polynomial F :=
  List.prod <| (List.range n).map fun i => 
    if f i ≠ p.eval (ωs i)
    then X - (C (ωs i))
    else C 1

section

variable {f ωs : ℕ → F} {p : Polynomial F}

@[simp]
lemma elocPoly_zero : ElocPoly 0 ωs f p = C 1 := rfl

@[simp]
lemma elocPoly_one :
  ElocPoly 1 ωs f p = if f 0 ≠ p.eval (ωs 0) then X - (C (ωs 0)) else C 1 := by
  simp [ElocPoly, List.range_succ]

@[simp]
lemma elocPoly_two :
  ElocPoly 2 ωs f p = 
  if f 1 = eval (ωs 1) p 
  then if f 0 = eval (ωs 0) p then C 1 
       else X - C (ωs 0)
  else if f 0 = eval (ωs 0) p then X - C (ωs 1)
       else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

@[simp]
lemma elocPoly_succ :
  ElocPoly (n + 1) ωs f p =
  ElocPoly n ωs f p * 
    if f n ≠ p.eval (ωs n)
    then X - (C (ωs n))
    else C 1 := by
  conv_lhs => unfold ElocPoly
  rw [List.range_succ, List.map_append, List.prod_append, ←ElocPoly.eq_def]
  simp

lemma roots_of_eloc_poly {x : F}
  (h : (ElocPoly n ωs f p).eval x = 0) : 
  ∃ i, i < n ∧ f i ≠ p.eval (ωs i) := by
  induction' n with n ih generalizing x
  · aesop
  · rw [elocPoly_succ, Polynomial.eval_mul, mul_eq_zero] at h
    rcases h with heval | heval
    · obtain ⟨i, _⟩ := ih heval
      aesop (add safe [(by existsi i), (by omega)])
    · aesop (add safe (by use n))

lemma errors_are_roots_of_elocPoly {i : ℕ}
  (hi : i < n) (h : f i ≠ p.eval (ωs i)) : (ElocPoly n ωs f p).eval (ωs i) = 0 := by
  induction' n with n ih
  · aesop
  · by_cases i = n
    · aesop
    · have : i < n := by omega
      aesop

@[simp]
lemma elocPoly_ne_zero : ElocPoly n ωs f p ≠ 0 := by
  induction' n with n _
  · simp
  · aesop (add simp [sub_eq_zero]) (add safe forward (Polynomial.X_ne_C (ωs n)))

@[simp]
lemma eloc_poly_deg 
  : (ElocPoly (ωs := ωs) f p).natDegree = Δ₀(f, p.eval ∘ ωs) := by
  revert f ωs p 
  unfold Function.comp
  induction n with
  | zero => 
    simp only [eloc_poly_zero, map_one, natDegree_one, hamming_zero_eq_dist] 
    intro f ωs p
    ext x
    exact Fin.elim0 x
  | succ n ih => 
    intro f ωs p 
    rw [eloc_poly_succ
    , Polynomial.natDegree_mul (by simp) (by {
      simp
      by_cases hif: f (Fin.last n) = eval (ωs (Fin.last n)) p
        <;> try simp [hif]
      intro contr 
      have h : X = C (ωs (Fin.last n)):= by 
        conv =>
          rhs
          rw [←zero_add (C _), ←contr]
          rfl
        ring
      exact Polynomial.X_ne_C _ h
    })]
    by_cases hif: f (Fin.last n) = eval (ωs (Fin.last n)) p
      <;> try simp only [hif, ih]
    · simp [hammingDist]
      apply Finset.card_eq_of_equiv
      simp
      exact ⟨fun ⟨x, hx⟩ => ⟨x, by simp [hx]⟩
        , fun ⟨x, hx⟩ => ⟨⟨x.val,by {
            have hx_le : x.val ≤ n := Fin.le_last _
            have hx_ne : x.val ≠ n := by {
              intro contr
              have hx_eq : x = Fin.last n := by {
                apply Fin.ext
                simp [contr]
              }
              subst hx_eq
              tauto
            }
            omega
          }⟩,  by aesop⟩
          , by simp [Function.LeftInverse]
          , by simp [Function.RightInverse
          , Function.LeftInverse] ⟩
    · simp [hif, hammingDist]
      symm
      rw [Finset.card_eq_succ]
      exists (Fin.last n)
      exists Finset.filter 
        (fun i => ¬f i = eval (ωs i) p ∧ i ≠ Fin.last n) 
        (Fintype.elems (α := Fin n.succ)) 
      apply And.intro <;> try simp
      apply And.intro
      · apply Finset.ext
        intro a
        apply Iff.intro <;> intro hhh
        · rw [Finset.mem_insert] at hhh 
          rcases hhh with hhh | hhh
          subst hhh
          simp [hif]
          simp at hhh
          simp [hhh]
        · simp at hhh
          simp
          by_cases haa : a = Fin.last n <;> try simp [haa, Fintype.elems, hhh]
      · apply Finset.card_eq_of_equiv
        simp
        exact ⟨fun ⟨x, hx⟩ => ⟨⟨x.val,by {
              have hx_le : x.val ≤ n := Fin.le_last _
              have hx_ne : x.val ≠ n := by {
                intro contr
                have hx_eq : x = Fin.last n := by {
                  apply Fin.ext
                  simp [contr]
                }
                subst hx_eq
                tauto
              }
              omega
            }⟩, by simp [hx]⟩
          , fun ⟨x, hx⟩ => ⟨⟨x, Nat.lt_succ_of_lt (by simp)⟩,  
              by {
                simp [Fintype.elems]
                rcases x with ⟨x, hx_lt⟩ 
                dsimp at hx
                simp [hx]
                intro contr
                have h : x = n := by {
                  rw [←Fin.val_inj] at contr
                  exact contr
                }
                omega
              }⟩
              , by simp [Function.LeftInverse]
              , by simp [Function.RightInverse
              , Function.LeftInverse] ⟩

end
