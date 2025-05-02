import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

import ArkLib.Data.CodingTheory.Basic

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}

open Polynomial

section Hoist

/-
  Basic ad-hoc lifting;
  - `liftF : (Fin n → α) → ℕ → α`
  - `liftF` : (ℕ → α) → Fin n → α
  These invert each other assuming appropriately-bounded domains.

  These are specialised versions of true lifts that uses `Nonempty` / `Inhabited`
  and take the complement of the finite set which is the domain of the function being lifted.
-/

variable [Zero α] {f : ℕ → α} {f' : Fin n → α}

/--
  `liftF` lifts functions over domains `Fin n` to functions over domains `ℕ`
  by returning `0` on points `≥ n`.
-/
def liftF (f : Fin n → α) : ℕ → α :=
  fun m ↦ if h : m < n then f ⟨m, h⟩ else 0

/--
  `liftF'` lifts functions over domains `ℕ` to functions over domains `Fin n`
  by taking the obvious injection.
-/
def liftF' (f : ℕ → α) : Fin n → α :=
  fun m ↦ f m.1

@[simp]
lemma liftF_succ {f : Fin (n + 1) → α} : liftF f n = f ⟨n, Nat.lt_add_one _⟩ := by
  aesop (add simp liftF)

lemma liftF'_liftF_of_lt {k : Fin m} (h : k < n) :
  liftF' (n := m) (liftF (n := n) f') k = f' ⟨k, by omega⟩ := by
  aesop (add simp [liftF, liftF'])

@[simp]
lemma liftF'_liftF_succ {f : Fin (n + 1) → α} {x : Fin n} :
  liftF' (liftF (n := n + 1) f) x = f x.castSucc := by
  aesop (add simp [liftF, liftF']) (add safe (by omega))

@[simp]
protected lemma liftF'_liftF : Function.LeftInverse liftF' (liftF (α := α) (n := n)) := by
  aesop (add simp [Function.LeftInverse, liftF, liftF'])

lemma liftF_liftF'_of_lt (h : m < n) : liftF (liftF' (n := n) f) m = f m := by
  aesop (add simp liftF)

@[simp]
lemma liftF_liftF'_succ : liftF (liftF' (n := n + 1) f) n = f n := by
  aesop (add simp liftF)

abbrev contract (m : ℕ) (f : Fin n → α) := liftF (liftF' (n := m) (liftF f))

lemma contract_eq_liftF_of_lt {k : ℕ} {f : Fin n → α} (h₁ : k < m) :
  contract m f k = liftF f k := by
  aesop (add simp [contract, liftF, liftF'])

attribute [simp] contract.eq_def

lemma eval_liftF_of_lt {ωs : Fin m → F} (h : n < m) : eval (liftF ωs n) p = eval (ωs ⟨n, h⟩) p := by
  aesop (add simp liftF)

end Hoist

section BW

variable [DecidableEq F]

noncomputable def ElocPoly (n : ℕ) (ωs f : ℕ → F) (p : Polynomial F) : Polynomial F :=
  List.prod <| (List.range n).map fun i => 
    if f i = p.eval (ωs i)
    then 1
    else X - C (ωs i)

section

variable {ωs f : ℕ → F}

@[simp]
lemma elocPoly_zero : ElocPoly 0 ωs f p = 1 := rfl

@[simp]
lemma elocPoly_one :
  ElocPoly 1 ωs f p = if f 0 ≠ p.eval (ωs 0) then X - (C (ωs 0)) else 1 := by
  simp [ElocPoly, List.range_succ]

@[simp]
lemma elocPoly_two :
  ElocPoly 2 ωs f p = 
  if f 1 = eval (ωs 1) p 
  then if f 0 = eval (ωs 0) p then 1 
       else X - C (ωs 0)
  else if f 0 = eval (ωs 0) p then X - C (ωs 1)
       else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

@[simp]
lemma elocPoly_succ :
  ElocPoly (n + 1) ωs f p =
  ElocPoly n ωs f p * 
    if f n = p.eval (ωs n)
    then 1
    else X - C (ωs n) := by
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

section

lemma elocPoly_congr {ωs' f' : ℕ → F}
  (h₁ : ∀ {m}, m < n → ωs m = ωs' m) (h₂ : ∀ {m}, m < n → f m = f' m) :
  ElocPoly n ωs f = ElocPoly n ωs' f' := by
  ext p
  unfold ElocPoly
  rw [
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    List.pmap_eq_map_attach, List.pmap_eq_map_attach
  ]
  aesop (add simp List.mem_range)

noncomputable def ElocPolyF (ωs f : Fin n → F) (p : Polynomial F) : Polynomial F :=
  ElocPoly n (liftF ωs) (liftF f) p

@[simp]
lemma elocPolyF_eq_elocPoly : ElocPolyF (n := n) (liftF' ωs) (liftF' f) = ElocPoly n ωs f := 
  elocPoly_congr liftF_liftF'_of_lt liftF_liftF'_of_lt

@[simp]
lemma elocPolyF_eq_elocPoly' {ωs f : Fin n → F} :
  ElocPolyF ωs f p = ElocPoly n (liftF ωs) (liftF f) p := rfl

lemma elocPoly_leftF_leftF_eq_contract {ωs f : Fin m → F} :
  ElocPoly n (liftF ωs) (liftF f) =
  ElocPoly n (contract n ωs) (contract n f) := by
  rw [elocPoly_congr contract_eq_liftF_of_lt contract_eq_liftF_of_lt]
  
end

@[simp]
lemma eloc_poly_deg {ωs f : Fin n → F} : (ElocPolyF ωs f p).natDegree = Δ₀(f, p.eval ∘ ωs) := by
  rw [elocPolyF_eq_elocPoly']
  induction' n with n ih
  · simp only [elocPoly_zero, map_one, natDegree_one, hamming_zero_eq_dist]
    exact funext_iff.2 (Fin.elim0 ·)
  · rw [
      elocPoly_succ,
      natDegree_mul (by simp)
                    (by aesop (erase simp liftF_succ)
                              (add simp [sub_eq_zero])
                              (add safe forward (X_ne_C (liftF ωs n)))),
      elocPoly_leftF_leftF_eq_contract
    ]
    aesop (config := {warnOnNonterminal := false}) (add simp [
      hammingDist.eq_def, Finset.card_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ
    ]) <;> (apply Finset.sum_congr rfl; aesop (add safe (by omega)))

end

end BW

end BerlekampWelch
