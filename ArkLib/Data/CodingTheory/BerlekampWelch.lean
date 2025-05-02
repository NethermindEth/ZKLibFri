import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

import ArkLib.Data.CodingTheory.Basic

variable {F : Type} [Field F] [DecidableEq F]

open Polynomial

noncomputable def ElocPoly {n : ℕ} {ωs : Fin n → F} 
  (f : Fin n → F) (p : Polynomial F) : Polynomial F
  := match n with 
  | 0 => C 1
  | n + 1 => List.prod <| List.map (fun i => 
      let i := Fin.ofNat' n.succ i
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else Polynomial.C 1) (List.range n.succ) 

lemma eloc_poly_nonzero_def {n : ℕ} {ωs : Fin n → F} 
  {f : Fin n → F} {p : Polynomial F} (hne: n ≠ 0) :
    ElocPoly (ωs := ωs) f p = (List.prod <| List.map (fun i => 
      let i := @Fin.ofNat' n (neZero_iff.2 hne) i
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else Polynomial.C 1) (List.range n) ) := by
  rcases n with n | n <;> try simp at hne 
  simp [ElocPoly]

@[simp]
lemma eloc_poly_zero {f : Fin 0 → F} {ωs : Fin 0 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = C 1 := by simp [ElocPoly]

@[simp]
lemma eloc_poly_one {f : Fin 1 → F} {ωs : Fin 1 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = let i := Fin.ofNat' 1 0
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else Polynomial.C 1 := by
  simp [ElocPoly, List.range_succ]

lemma eloc_poly_two {f : Fin 2 → F} {ωs : Fin 2 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = 
      if f 1 = eval (ωs 1) p 
      then if f 0 = eval (ωs 0) p then Polynomial.C 1 
           else (X - C (ωs 0)) 
      else if f 0 = eval (ωs 0) p then (X - C (ωs 1)) 
           else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

lemma eloc_poly_succ {n : ℕ} 
  {f : Fin (n + 1) → F} {ωs : Fin (n + 1) → F} {p : Polynomial F} :
  ElocPoly (ωs := ωs) f p = 
      (ElocPoly (ωs := ωs ∘ Fin.castSucc) (f ∘ Fin.castSucc) p)* (let i := Fin.last n
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else Polynomial.C 1) := by
  conv => 
    lhs 
    unfold ElocPoly; rfl
  rcases n with n | n 
  · simp [ElocPoly, List.range_succ]
  · simp only [Nat.succ_eq_add_one, Fin.ofNat'_eq_cast, ne_eq, ite_not, ite_mul]
    rw [List.range_succ]
    have h : Fin.last n.succ = ↑n + 1 := by
      apply Fin.ext
      simp
      rw [Fin.val_add_one] 
      have h : ↑n ≠ Fin.last n.succ := by
        intro contr
        have h : (↑n : Fin (n + 1 +1)).val = (Fin.last n.succ).val := by
          rw [contr]
        simp [Fin.last] at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
      simp [h]
      rw [Nat.mod_eq_of_lt (by omega)]  
    rw [h]
    simp 
    by_cases hif : f (↑n + 1) = eval (ωs (↑n + 1)) p 
    · simp [hif]
      rw [eloc_poly_nonzero_def (by omega)]
      simp
      rw [List.prod_eq_foldl, List.prod_eq_foldl]
      apply congr 
      rfl 
      rw [List.map_eq_map_iff]
      intro i hi
      have h_i_lt : i < n.succ := by aesop
      have hh: (↑i : Fin (n+1+1)) = (↑i : Fin (n+1)).castSucc := by 
        apply Fin.ext
        simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.natCast_def]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hh]
    · simp [hif]
      left
      simp [ElocPoly]
      rw [List.prod_eq_foldl, List.prod_eq_foldl]
      apply congr 
      rfl 
      rw [List.map_eq_map_iff]
      intro i hi
      have h_i_lt : i < n.succ := by aesop
      have hh: (↑i : Fin (n+1+1)) = (↑i : Fin (n+1)).castSucc := by 
        apply Fin.ext
        simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.natCast_def]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hh]
 
lemma roots_of_eloc_poly 
  {n : ℕ} 
  {f : Fin n → F} 
  {ωs : Fin n → F} 
  {p : Polynomial F} 
  {x : F} 
  (h : (ElocPoly (ωs := ωs) f p).eval x = 0) : 
  ∃ i : Fin n, f i ≠ p.eval (ωs i)  := by
  revert f p x ωs 
  induction n with
  | zero =>
    aesop
  | succ n ih =>
    intro ωs f p x heval
    rw [eloc_poly_succ
    , Polynomial.eval_mul
    , mul_eq_zero] at heval
    rcases heval with heval | heval
    · specialize (ih heval)
      rcases ih with ⟨i, ih⟩
      exists i
      simp at ih
      simp [ih]
    · simp at heval
      by_cases hif : ωs (Fin.last n) = eval (f (Fin.last n)) p
        <;> simp [hif] at heval
      · tauto

lemma errors_are_roots_of_eloc_poly 
  {n : ℕ} 
  {f : Fin n → F} 
  {ωs : Fin n → F} 
  {p : Polynomial F} 
  {i : Fin n} 
  (h : f i ≠ p.eval (ωs i)) :
  (ElocPoly (ωs := ωs) f p).eval (ωs i) = 0 := by
  revert f ωs i p
  induction n with
  | zero => simp [ElocPoly]
  | succ n ih => 
    intro f ωs p i h
    rw [eloc_poly_succ]
    simp [Polynomial.eval_mul]
    by_cases hi : i = Fin.last n
    · subst hi
      simp [h]
    · have hi_coe : ∃ j : Fin n, i = Fin.castSucc j := by
          exists ⟨i, by {
              have hn : i ≠ Fin.last n := by simp [hi]
              rw [←Fin.lt_last_iff_ne_last] at hn
              aesop
          }⟩
      rcases hi_coe with ⟨j, hi_coe⟩
      subst hi_coe
      have hj : ωs j.castSucc = (ωs ∘ Fin.castSucc) j := by rfl
      rw [hj]
      by_cases hif : f (Fin.last n) = eval (ωs (Fin.last n)) p 
        <;> try simp only [hif, ite_true, ite_false, Polynomial.eval_mul, mul_eq_zero]
      · apply ih 
         ; try simp [Function.comp, h]
      · left ; apply ih 
         ; try simp [Function.comp, h]

variable 
  {n : ℕ} 
  {f : Fin n → F} 
  {ωs : Fin n → F} 
  {p : Polynomial F} 

@[simp]
lemma eloc_poly_ne_zero :
    ElocPoly (ωs := ωs) f p ≠ 0 := by
  revert f ωs p
  induction n with
  | zero => simp [ElocPoly]
  | succ n ih => 
    intros f ωs p
    rw [eloc_poly_succ]
    apply mul_ne_zero ih
    simp
    by_cases hif : f (Fin.last n) = eval (ωs (Fin.last n)) p 
      <;> try simp [hif]
    intro contr 
    have h : X = C (ωs (Fin.last n)):= by 
      conv =>
        rhs
        rw [←zero_add (C _), ←contr]
        rfl
      ring
    exact Polynomial.X_ne_C _ h

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
