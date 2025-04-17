import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.FieldSimp

class NonBinaryField  
  (F : Type) extends Field F where 
  char_neq_2 : (2 : F) ≠ 0 

export NonBinaryField (char_neq_2)

attribute [simp] char_neq_2

section NonBinaryField

variable {F : Type} [NonBinaryField F]

@[simp]
lemma two_mul_inv_two : (2 : F) * 2⁻¹ = 1 := by simp

@[simp]
lemma inv_two_mul_two : 2⁻¹ * (2 : F) = 1 := by simp

end NonBinaryField

variable {F: Type} [Field F]

section

open Polynomial

private lemma coeffs_of_comp_minus_x_pos_degree {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · aesop (add simp coeff_X) 
  · rintro _ _ _ (_ | _) <;> aesop (add simp [Nat.even_add_one, Nat.even_iff])
  · rintro _ _ _ _ (_ | _) <;> aesop
    
theorem coeffs_of_comp_minus_x {f : Polynomial F} {n : ℕ}  :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
    by_cases hpos : 0 < f.degree 
    · rw [coeffs_of_comp_minus_x_pos_degree hpos]
    · have : f.natDegree = 0 := by aesop (add simp natDegree_pos_iff_degree_pos.symm)
      cases n <;> aesop (add simp natDegree_eq_zero)

private lemma comp_x_square_coeff_pos_deg {f : Polynomial F} {n : ℕ} (h : 0 < f.degree):
  (f.comp (X * X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · rintro _ _ (_ | _ | _ | n) <;> try simp [coeff_X]
    split_ifs with h₁ h₂ <;> [symm at h₂; rfl; rfl]
    aesop (add simp [Nat.div_eq_iff_eq_mul_left, even_iff_two_dvd])
  · rintro _ _ _ (_ | _ | n) <;> try simp [←mul_assoc]
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    aesop (add simp [Nat.even_iff, Nat.odd_iff], safe (by omega))
  · rintro p a hpdeg ih (_ | _ | n) <;> try simp_all
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    aesop (add safe (by omega))

theorem comp_x_square_coeff {f : Polynomial F} {n : ℕ} :
  (f.comp (Polynomial.X * Polynomial.X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
    by_cases hpos : 0 < f.degree 
    · rw [comp_x_square_coeff_pos_deg hpos]
    · generalize hdeg : f.degree = d 
      rcases d with _ | d 
      · rw [WithBot.none_eq_bot, degree_eq_bot] at hdeg 
        simp [hdeg]
      · rw [WithBot.some_eq_coe] at hdeg 
        rw [hdeg] at hpos
        have hpos : d = 0 := by aesop 
        have hdeg := natDegree_eq_of_degree_eq_some hdeg 
        subst hpos
        rw [Polynomial.natDegree_eq_zero] at hdeg 
        rcases hdeg with ⟨x, hdeg⟩ 
        rw [←hdeg]
        rcases n with _ | n <;> try simp 
        by_cases hif : Even (n + 1) <;> try simp [hif]
        rcases n with _ | n <;> try simp 
        · simp at hif 
        · have h_plus_1 : (n + 1 + 1)/ 2 = n/2 + 1 := by 
            have h_n_1_1 : n + 1 + 1 = n + 2 := by omega 
            rw [h_n_1_1,
                Nat.add_div_right _ (by omega)]
          rw [h_plus_1]
          simp 

end   
