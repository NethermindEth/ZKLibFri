import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

theorem polynomial_sum_ext.{u, u_1}
  {R : Type u} 
  [Semiring R] 
  {S : Type u_1} 
  [AddCommMonoid S] 
  {p : Polynomial R} {f g : ℕ → R → S}  
  (h : ∀ i x, f i x = g i x)
  : p.sum f = p.sum g := by
  aesop (add simp [Polynomial.sum])
