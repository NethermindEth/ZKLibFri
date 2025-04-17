import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Embedding.Basic

import ZKLib.ProofSystem.Fri.EvenAndOdd.ToMathlib

def erase_odd (s : Finset ℕ) : Finset ℕ := s.filter Even
def erase_even (s : Finset ℕ) : Finset ℕ := s.filter Odd

@[simp]
lemma erase_odd_empty :
    erase_odd ∅ = ∅ := by rfl

lemma erase_odd_def {s : Finset ℕ}:
    erase_odd s = s.filter Even := by rfl 

@[simp]
lemma erase_even_empty :
    erase_even ∅ = ∅ := by rfl 
      
lemma erase_even_def {s : Finset ℕ}:
    erase_even s = s.filter Odd := by rfl 

def shift_left (s : Finset ℕ) : Finset ℕ :=
  s.filterMap 
    (fun n => match n with 
      | 0 => .none 
      | n + 1 => .some n
      )
    (by aesop)

@[simp]
lemma shift_left_empty :
    shift_left ∅ = ∅ := by rfl 

lemma shift_left_def {s : Finset ℕ}:
    shift_left s = s.filterMap 
    (fun n => match n with 
      | 0 => .none 
      | n + 1 => .some n
      )
    (by aesop)
 := by rfl 

def mul_by_2 (s : Finset ℕ) : Finset ℕ :=
  s.map ⟨fun n => 2 * n, by {
    intro a b 
    simp 
  }⟩ 

@[simp]
lemma mul_by_empty :
    mul_by_2 ∅ = ∅ := by rfl 

lemma mul_by_2_def {s : Finset ℕ}:
    mul_by_2 s = s.map ⟨fun n => 2 * n, by {
      intro a b 
      simp 
    }⟩  := by rfl 

def divide_by_2 (s : Finset ℕ) : Finset ℕ :=
  (erase_odd s).image (fun n => n / 2)

@[simp]
lemma divide_by_2_empty :
    divide_by_2 ∅ = ∅ := by rfl 

lemma divide_by_2_def {s : Finset ℕ} :
    divide_by_2 s = (erase_odd s).image (fun n => n / 2) := by rfl

@[simp]
theorem erase_odd_mem 
  {s : Finset ℕ}
  {n : ℕ}
  : n ∈ (erase_odd s) ↔ Even n ∧ n ∈ s := by 
  simp [erase_odd] 
  tauto 

@[simp]
theorem erase_even_mem 
  {s : Finset ℕ}
  {n : ℕ}
  : n ∈ (erase_even s) ↔ Odd n ∧ n ∈ s := by 
  simp [erase_even] 
  tauto 

@[simp]
theorem mul_by_2_mem {s : Finset ℕ} {d : ℕ} :
    d ∈ mul_by_2 s ↔ Even d ∧ (d / 2) ∈ s := by 
  simp [mul_by_2]
  apply Iff.intro <;> intro h
  · rcases h with ⟨a, ⟨h1, h2⟩⟩ 
    rw [←h2]
    simp [h1]
  · exists d / 2
    simp [h]
    rw [Nat.even_iff] at h
    omega 

@[simp]
theorem divide_by_2_mem {s : Finset ℕ} {d : ℕ} :
  d ∈ divide_by_2 s ↔ 2 * d ∈ s := by
  simp [divide_by_2] 
  apply Iff.intro <;> intro h
  · rcases h with ⟨a, ⟨h1, h2⟩⟩ 
    rw [←h2]
    rcases h1 with ⟨ha_even, ha_mem⟩ 
    rw [Nat.even_iff] at ha_even 
    rw [Nat.mul_div_eq_iff_dvd.2 (by omega)]
    exact ha_mem 
  · exists (2 * d)
    simp [h]
    
@[simp]
theorem shift_left_mem {s : Finset ℕ} {d : ℕ} : d ∈ shift_left s ↔ (d + 1) ∈ s := by 
  simp [shift_left]
  aesop  
