import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

variable {F : Type} [Field F] [DecidableEq F]

open Polynomial

noncomputable def ElocPoly {n : ℕ} {ωs : Fin n → F} 
  (f : Fin n → F) (p : Polynomial F) : Polynomial F
  := match n with 
  | 0 => C 1
  | n + 1 => List.prod <| List.map (fun i => 
      let i := Fin.ofNat' n.succ i
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) (List.range n.succ) 

lemma eloc_poly_nonzero_def {n : ℕ} {ωs : Fin n → F} 
  {f : Fin n → F} {p : Polynomial F} (hne: n ≠ 0) :
    ElocPoly (ωs := ωs) f p = (List.prod <| List.map (fun i => 
      let i := @Fin.ofNat' n (neZero_iff.2 hne) i
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) (List.range n) ) := by
  rcases n with n | n <;> try simp at hne 
  simp [ElocPoly]

@[simp]
lemma eloc_poly_zero {f : Fin 0 → F} {ωs : Fin 0 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = C 1 := by simp [ElocPoly]

@[simp]
lemma eloc_poly_one {f : Fin 1 → F} {ωs : Fin 1 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = let i := Fin.ofNat' 1 0
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X := by
  simp [ElocPoly, List.range_succ]

lemma eloc_poly_two {f : Fin 2 → F} {ωs : Fin 2 → F} {p : Polynomial F} :
    ElocPoly (ωs := ωs) f p = 
      if f 1 = eval (ωs 1) p 
      then if f 0 = eval (ωs 0) p then X * X 
           else (X - C (ωs 0)) * X
      else if f 0 = eval (ωs 0) p then X * (X - C (ωs 1)) 
           else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

lemma eloc_poly_succ {n : ℕ} 
  {f : Fin (n + 1) → F} {ωs : Fin (n + 1) → F} {p : Polynomial F} :
  ElocPoly (ωs := ωs) f p = 
      (ElocPoly (ωs := ωs ∘ Fin.castSucc) (f ∘ Fin.castSucc) p)* (let i := Fin.last n
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) := by
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
 
lemma roots_of_eloc_poly {f : Fin n → F} {p : Polynomial F} {x : F} 
  (hne : x ≠ 0) 
    (h : (ElocPoly (ωs := ωs) f p).eval x = 0) : 
  ∃ i : Fin n, f i ≠ p.eval (ωs i)  := by
  have hn := NeZero.ne n 
  revert f p x ωs 
  induction n with
  | zero =>
    aesop
  | succ n ih =>
    intro ωs f p x hne heval
    simp [ElocPoly] at heval
  
