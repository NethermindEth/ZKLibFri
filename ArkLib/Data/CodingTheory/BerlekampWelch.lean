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
  | n + 1 => List.foldl (fun acc i => 
      let i := Fin.ofNat' n.succ i
      let ω := ωs i 
      acc * if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) (C 1) (List.range n.succ) 

lemma eloc_poly_nonzero_def {n : ℕ} {ωs : Fin n → F} 
  {f : Fin n → F} {p : Polynomial F} (hne: n ≠ 0) :
    ElocPoly (ωs := ωs) f p = List.foldl (fun acc i => 
      let i := @Fin.ofNat' n (neZero_iff.2 hne) i
      let ω := ωs i 
      acc * if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) (C 1) (List.range n)  := by
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

lemma eloc_poly_succ {n : ℕ} [NeZero n]
  {f : Fin (n + 1) → F} {ωs : Fin (n + 1) → F} {p : Polynomial F} {x : F} :
  ElocPoly (ωs := ωs) f p = 
    (ElocPoly (ωs := ωs ∘ Fin.castSucc) (f ∘ Fin.castSucc) p) 
      * (let i := Fin.ofNat' n.succ n
      let ω := ωs i 
      if f i ≠ p.eval ω then (X - (Polynomial.C ω)) else X) := by
  have hn := NeZero.ne n 
  revert f ωs p x hn
  induction n with
  | zero => 
    aesop
  | succ n ih => 
    intro f ωs p x hn
    by_cases h_n_z : n = 0
    · subst h_n_z 
      simp [eloc_poly_two]
    · conv =>
        lhs 
        unfold ElocPoly 
        rfl 
      simp
      rw [List.range_succ]
      simp
      by_cases hif :f (↑n + 1) = eval (ωs (↑n + 1)) p
      · simp [hif]
        rw [List.range_succ]
        simp
        by_cases hif : f ↑n = eval (ωs ↑n) p
        · simp [hif]
          have hhh 
            := eloc_poly_nonzero_def 
                (p := p) 
                (f := f ∘ Fin.castSucc ∘ Fin.castSucc)
                (ωs := ωs ∘ Fin.castSucc ∘ Fin.castSucc) h_n_z
          simp at hhh
          let f' := λ (acc : F[X]) (i : ℕ) ↦
                      if (f (↑i : Fin (n + 1 + 1))) = (eval (ωs ↑i) p)
                      then acc * X
                      else acc * (X - C (ωs ↑i))
          rw [List.foldl_ext (g := f')] at hhh











    
    








  
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
  
