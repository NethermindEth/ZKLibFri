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
protected def liftF (f : Fin n → α) : ℕ → α :=
  fun m ↦ if h : m < n then f ⟨m, h⟩ else 0

/--
  `liftF'` lifts functions over domains `ℕ` to functions over domains `Fin n`
  by taking the obvious injection.
-/
protected def liftF' (f : ℕ → α) : Fin n → α :=
  fun m ↦ f m.1

open BerlekampWelch (liftF liftF')

@[simp]
protected lemma liftF_succ {f : Fin (n + 1) → α} : liftF f n = f ⟨n, Nat.lt_add_one _⟩ := by
  aesop (add simp liftF)

protected lemma liftF'_liftF_of_lt {k : Fin m} (h : k < n) :
  liftF' (n := m) (liftF (n := n) f') k = f' ⟨k, by omega⟩ := by
  aesop (add simp [liftF, liftF'])

@[simp]
protected lemma liftF'_liftF_succ {f : Fin (n + 1) → α} {x : Fin n} :
  liftF' (liftF (n := n + 1) f) x = f x.castSucc := by
  aesop (add simp [liftF, liftF']) (add safe (by omega))

@[simp]
protected lemma liftF'_liftF : Function.LeftInverse liftF' (liftF (α := α) (n := n)) := by
  aesop (add simp [Function.LeftInverse, liftF, liftF'])

protected lemma liftF_liftF'_of_lt (h : m < n) : liftF (liftF' (n := n) f) m = f m := by
  aesop (add simp liftF)

@[simp]
protected lemma liftF_liftF'_succ : liftF (liftF' (n := n + 1) f) n = f n := by
  aesop (add simp liftF)

protected lemma liftF_eval {f : Fin n → α} {i : Fin n} :
  liftF f i.val = f i := by
  aesop (add simp liftF)

protected abbrev contract (m : ℕ) (f : Fin n → α) := liftF (liftF' (n := m) (liftF f))

open BerlekampWelch (contract)

protected lemma contract_eq_liftF_of_lt {k : ℕ} (h₁ : k < m) :
  contract m f' k = liftF f' k := by
  aesop (add simp [contract, liftF, liftF'])

attribute [simp] contract.eq_def

protected lemma eval_liftF_of_lt {f : Fin m → F} (h : n < m) :
  eval (liftF f n) p = eval (f ⟨n, h⟩) p := by
  aesop (add simp liftF)

end Hoist

section BW

variable [DecidableEq F]

protected noncomputable def ElocPoly (n : ℕ) (ωs f : ℕ → F) (p : Polynomial F) : Polynomial F :=
  List.prod <| (List.range n).map fun i => 
    if f i = p.eval (ωs i)
    then 1
    else X - C (ωs i)

section

open BerlekampWelch (ElocPoly)

variable {ωs f : ℕ → F}

@[simp]
protected lemma elocPoly_zero : ElocPoly 0 ωs f p = 1 := rfl

@[simp]
protected lemma elocPoly_one :
  ElocPoly 1 ωs f p = if f 0 ≠ p.eval (ωs 0) then X - (C (ωs 0)) else 1 := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_two :
  ElocPoly 2 ωs f p = 
  if f 1 = eval (ωs 1) p 
  then if f 0 = eval (ωs 0) p then 1 
       else X - C (ωs 0)
  else if f 0 = eval (ωs 0) p then X - C (ωs 1)
       else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_succ :
  ElocPoly (n + 1) ωs f p =
  ElocPoly n ωs f p * 
    if f n = p.eval (ωs n)
    then 1
    else X - C (ωs n) := by
  conv_lhs => unfold ElocPoly
  rw [List.range_succ, List.map_append, List.prod_append, ←ElocPoly.eq_def]
  simp

open BerlekampWelch (elocPoly_succ) in
protected lemma roots_of_eloc_poly {x : F}
  (h : (ElocPoly n ωs f p).eval x = 0) : 
  ∃ i, i < n ∧ f i ≠ p.eval (ωs i) := by
  induction' n with n ih generalizing x
  · aesop
  · rw [elocPoly_succ, Polynomial.eval_mul, mul_eq_zero] at h
    rcases h with heval | heval
    · obtain ⟨i, _⟩ := ih heval
      aesop (add safe [(by existsi i), (by omega)])
    · aesop (add safe (by use n))

protected lemma errors_are_roots_of_elocPoly {i : ℕ}
  (hi : i < n) (h : f i ≠ p.eval (ωs i)) : (ElocPoly n ωs f p).eval (ωs i) = 0 := by
  induction' n with n ih
  · aesop
  · by_cases i = n
    · aesop
    · have : i < n := by omega
      aesop

@[simp]
protected lemma elocPoly_ne_zero : ElocPoly n ωs f p ≠ 0 := by
  induction' n with n _
  · simp
  · aesop (add simp [sub_eq_zero]) (add safe forward (Polynomial.X_ne_C (ωs n)))

section

open BerlekampWelch (liftF liftF' contract liftF_liftF'_of_lt liftF_liftF'_of_lt)

protected lemma elocPoly_congr {ωs' f' : ℕ → F}
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

open BerlekampWelch (elocPoly_congr contract_eq_liftF_of_lt)

noncomputable def ElocPolyF (ωs f : Fin n → F) (p : Polynomial F) : Polynomial F :=
  ElocPoly n (liftF ωs) (liftF f) p

@[simp]
protected lemma elocPolyF_eq_elocPoly :
  ElocPolyF (n := n) (liftF' ωs) (liftF' f) = ElocPoly n ωs f := 
  elocPoly_congr liftF_liftF'_of_lt liftF_liftF'_of_lt

@[simp]
protected lemma elocPolyF_eq_elocPoly' {ωs f : Fin n → F} :
  ElocPolyF ωs f p = ElocPoly n (liftF ωs) (liftF f) p := rfl

protected lemma elocPoly_leftF_leftF_eq_contract {ωs f : Fin m → F} :
  ElocPoly n (liftF ωs) (liftF f) =
  ElocPoly n (contract n ωs) (contract n f) := by
  rw [elocPoly_congr contract_eq_liftF_of_lt contract_eq_liftF_of_lt]

protected lemma errors_are_roots_of_elocPolyF {i : Fin n} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (ElocPolyF ωs f p).eval (ωs i) = 0 := by
  rw [←BerlekampWelch.liftF_eval (f := ωs)]
  aesop (config := {warnOnNonterminal := false})
  rw [BerlekampWelch.errors_are_roots_of_elocPoly 
    (i.isLt) 
    (by aesop (add simp [BerlekampWelch.liftF_eval]))]
  
end

open BerlekampWelch
  (elocPolyF_eq_elocPoly' elocPoly_leftF_leftF_eq_contract
   elocPoly_zero elocPoly_succ liftF liftF_succ)

@[simp]
lemma elocPolyF_deg {ωs f : Fin n → F} : (ElocPolyF ωs f p).natDegree = Δ₀(f, p.eval ∘ ωs) := by
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

noncomputable def E {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  X ^ (e - (Δ₀(f, p.eval ∘ ωs) : ℕ)) * ElocPolyF (ωs := ωs) f p

lemma E_natDegree 
  {e : ℕ} 
  {ωs f : Fin n → F} 
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) < e) : 
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


noncomputable def Q {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  p * (E ωs f p e)

lemma Q_natDegree 
  {e : ℕ} {ωs f : Fin n → F}
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) < e) : 
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

lemma y_i_E_omega_i_eq_Q_omega_i {e : ℕ} {i : Fin n} {ωs f : Fin n → F}:
  (Q ωs f p e).eval (ωs i) = (f i) * (E ωs f p e).eval (ωs i) := by
  unfold Q E
  by_cases hi : f i = p.eval (ωs i)
  · aesop 
  · aesop 
      (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
      (add simp [BerlekampWelch.errors_are_roots_of_elocPolyF])

lemma E_and_Q_unique {e : ℕ} 
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hnz_e : E' ≠ 0) (hnz_q : Q' ≠ 0)
  (hdeg_e : E'.natDegree = e) (hdeg_q : Q'.natDegree ≤ e + p.natDegree)
  (h : ∀ i : Fin n, 
    (f i) * E'.eval (ωs i) = Q'.eval (ωs i))
  (he : 2 * e < n - p.natDegree)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) < e)
  (h_diff : Function.Injective ωs)
  (hp : p ≠ 0)
  : (E ωs f p e) * Q' = E' * (Q ωs f p e) := by
  let R := E ωs f p e * Q' - E' * Q ωs f p e 
  have hr_deg : R.natDegree ≤ 2 * e + p.natDegree := by
    simp [R]
    apply Nat.le_trans (natDegree_add_le _ _)
    simp only [
      natDegree_mul E_ne_0 hnz_q,
      natDegree_neg,
      natDegree_mul hnz_e (Q_ne_0 hp)
      ]
    aesop (config := {warnOnNonterminal := false})
      (add simp [Nat.max_le, E_natDegree])
      (add safe forward (Q_natDegree h_ham))
      (add safe (by omega))
  by_cases hr : R = 0 
  · rw [←add_zero (E' * (Q _ _ _ _))
       , ←hr]
    ring
  · let roots := Multiset.ofList <| List.map ωs  
        (List.finRange n)
    have hsub : (⟨roots, by 
        rw [Multiset.coe_nodup, List.nodup_map_iff h_diff]        
         ;
        aesop 
          (add simp [Multiset.coe_nodup])
          (add simp [List.Nodup, List.pairwise_iff_get])
      ⟩ : Finset F).val ⊆ R.roots := by
      {
        intro x hx
        aesop (config := {warnOnNonterminal := false})
          (add simp [mem_roots, roots, R])
          (add simp [errors_are_roots_of_E])
          (add simp [y_i_E_omega_i_eq_Q_omega_i]) 
        rw [←h]
        ring
      }
    have hcard := card_le_degree_of_subset_roots hsub 
    aesop (add safe (by omega))

end

end BW

end BerlekampWelch
