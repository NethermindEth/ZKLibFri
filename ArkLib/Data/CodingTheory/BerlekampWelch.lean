import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Matrix.Mul 
import Mathlib.Data.Matrix.Reflection

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.ToMathlib

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

protected lemma liftF_ne_0 {f : Fin n → α} {i : ℕ}
  (h : liftF f i ≠ 0)
  : i < n := by
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
  · rw [elocPoly_succ, eval_mul, mul_eq_zero] at h
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
  · aesop (add simp [sub_eq_zero]) (add safe forward (X_ne_C (ωs n)))

@[simp]
protected lemma elocPoly_leading_coeff_one : (ElocPoly n ωs f p).leadingCoeff = 1 := by
  induction' n with n _ 
  · simp
  · aesop

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

protected lemma elocPolyF_eq_elocPoly' {ωs f : Fin n → F} :
  ElocPolyF ωs f p = ElocPoly n (liftF ωs) (liftF f) p := rfl

open BerlekampWelch (elocPolyF_eq_elocPoly')

protected lemma elocPoly_leftF_leftF_eq_contract {ωs f : Fin m → F} :
  ElocPoly n (liftF ωs) (liftF f) =
  ElocPoly n (contract n ωs) (contract n f) := by
  rw [elocPoly_congr contract_eq_liftF_of_lt contract_eq_liftF_of_lt]

@[simp]
protected lemma elocPolyF_ne_zero {ωs f : Fin m → F} :
  ElocPolyF ωs f p ≠ 0 := by
  aesop (add simp [BerlekampWelch.elocPoly_ne_zero, ElocPolyF])

protected lemma errors_are_roots_of_elocPolyF {i : Fin n} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (ElocPolyF ωs f p).eval (ωs i) = 0 := by
  rw [←BerlekampWelch.liftF_eval (f := ωs)]
  aesop (config := {warnOnNonterminal := false}) (add simp elocPolyF_eq_elocPoly')
  rw [
    BerlekampWelch.errors_are_roots_of_elocPoly i.isLt
    (by aesop (add simp [BerlekampWelch.errors_are_roots_of_elocPoly, BerlekampWelch.liftF_eval]))
  ]

@[simp]
protected lemma elocPolyF_leading_coeff_one {ωs f : Fin n → F}
  : (ElocPolyF ωs f p).leadingCoeff = 1 := by simp [ElocPolyF]

end

open BerlekampWelch
  (elocPolyF_eq_elocPoly' elocPoly_leftF_leftF_eq_contract
   elocPoly_zero elocPoly_succ liftF liftF_succ elocPolyF_leading_coeff_one)

section

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
  X ^ (e - (Δ₀(f, p.eval ∘ ωs) : ℕ)) * ElocPolyF ωs f p

lemma natDegree_E_eq_of_lt
  {e : ℕ} 
  {ωs f : Fin n → F} 
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (E ωs f p e).natDegree = e  
  := by
  aesop (add simp [E, natDegree_mul]) (add safe (by omega))

@[simp]
lemma E_ne_0 {e : ℕ} {ωs f : Fin n → F} : (E ωs f p e) ≠ 0 := by
  aesop (add simp E)

lemma errors_are_roots_of_E {i : Fin n} {e} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (E ωs f p e).eval (ωs i) = 0  := by
  aesop (add simp [E, BerlekampWelch.errors_are_roots_of_elocPolyF])

@[simp]
lemma leadingCoeff_E_eq_1 {e} {ωs f : Fin n → F} : (E ωs f p e).leadingCoeff = 1 := by simp [E]

@[simp]
lemma normUnit_E_eq_1 {e} {ωs f : Fin n → F} : normUnit (E ωs f p e) = 1 := by
  simp [E, normUnit_mul, normUnit, mul_eq_one_iff_eq_inv]
  rfl

lemma normalize_E_eq_E {e} {ωs f : Fin n → F} : normalize (E ωs f p e) = E ωs f p e := by
  simp [normalize_apply]

noncomputable def Q {n : ℕ} (ωs f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  p * (E ωs f p e)

lemma natDegree_Q_le_of_lt
  {e : ℕ} {ωs f : Fin n → F}
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (Q ωs f p e).natDegree ≤ e + p.natDegree := by
  by_cases p = 0 <;>
  aesop (add simp [Q, natDegree_mul, natDegree_E_eq_of_lt]) (add safe (by omega))

lemma Q_ne_zero_of_ne {e : ℕ} {ωs f : Fin n → F} (hne : p ≠ 0) : Q ωs f p e ≠ 0 := by
  aesop (add simp [Q])

lemma eval_Q_eq_mul_eval_E {e : ℕ} {i : Fin n} {ωs f : Fin n → F}:
  (Q ωs f p e).eval (ωs i) = f i * (E ωs f p e).eval (ωs i) := by
  by_cases f i = p.eval (ωs i) <;> 
  aesop (add simp [Q, E, BerlekampWelch.errors_are_roots_of_elocPolyF])

lemma E_and_Q_unique {e k : ℕ}
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hk : 1 ≤ k)
  (hp_deg: p.natDegree ≤ k - 1)
  (hnz_e : E' ≠ 0) (hnz_q : Q' ≠ 0)
  (hdeg_e : E'.natDegree = e) (hdeg_q : Q'.natDegree ≤ e + k - 1)
  (h : ∀ i : Fin n, (f i) * E'.eval (ωs i) = Q'.eval (ωs i))
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (hp : p ≠ 0)
  : E ωs f p e * Q' = E' * Q ωs f p e := by
  set p₁ := E ωs f p e * Q' with eqp₁
  set p₂ := E' * Q ωs f p e with eqp₂
  let range := Finset.image ωs Finset.univ
  by_contra! contra
  have : range.card = n := by
    simp [range, Finset.card_image_iff.2 (Set.injOn_of_injective h_diff)]
  have : range.card ≤ (p₁ - p₂).natDegree :=
    card_le_degree_of_subset_roots fun x hx ↦ by
      obtain ⟨x', rfl⟩ := show ∃ i, ωs i = x by aesop
      simp [sub_ne_zero.2 contra, p₁, p₂, eval_Q_eq_mul_eval_E, ←h x']
      ring
  have hr_deg : (p₁ - p₂).natDegree ≤ 2 * e + k - 1 := by
    have := natDegree_Q_le_of_lt h_ham
    apply Nat.le_trans (natDegree_add_le _ _)
    aesop (add simp [natDegree_mul, Q_ne_zero_of_ne, natDegree_E_eq_of_lt]) (add safe (by omega))
  aesop (add safe (by omega))

def BerlekampWelchMatrix [NeZero n]
  (e k : ℕ) (ωs f : Fin n → F) : Matrix (Fin n) (Fin (2 * e + k)) F := 
  Matrix.of fun i j => 
    let αᵢ := ωs i
    if ↑j < e then f i * αᵢ^(↑j : ℕ) else -αᵢ^(↑j - e)

def Rhs [NeZero n] (e : ℕ) (ωs f : Fin n → F) (i : Fin n) : F := 
  let αᵢ := ωs i
  (-(f i) * αᵢ^e)

def IsBerlekampWelchSolution [NeZero n] 
  (e k : ℕ) 
  (ωs f : Fin n → F)
  (v : Fin (2 * e + k) → F)
  : Prop 
  := Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v = Rhs e ωs f

omit [DecidableEq F] in
lemma is_berlekamp_welch_solution_ext [NeZero n]
  {e k : ℕ} 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h : ∀ i, (Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v) i  = -(f i) * (ωs i)^e)
  : IsBerlekampWelchSolution e k ωs f v := by
  aesop (add simp [IsBerlekampWelchSolution, Rhs])

noncomputable def E_and_Q_to_a_solution (e : ℕ) (E Q : Polynomial F) (i : Fin n) : F :=
  if i < e then E.toFinsupp i else Q.toFinsupp (i - e)

omit [DecidableEq F] in
@[simp]
lemma E_and_Q_to_a_solution_coeff 
  {e : ℕ} 
  {E Q : Polynomial F} 
  {i : Fin n}
  : E_and_Q_to_a_solution e E Q i = if i < e then E.coeff i else Q.coeff (i - e) := rfl

lemma E_and_Q_are_a_solution {e k : ℕ} [NeZero n]
  {ωs f : Fin n → F} {p : Polynomial F}
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (hk : 1 ≤ k)
  (hp_deg : p.natDegree ≤ k - 1) 
  (he : 2 * e < n - k + 1)
  : IsBerlekampWelchSolution e k ωs f (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) := by
  refine is_berlekamp_welch_solution_ext fun i ↦ ?p
  rw [←Matrix.mulVecᵣ_eq]
  simp [Matrix.mulVecᵣ, dotProduct]
  rw [Finset.sum_ite]
  simp [BerlekampWelchMatrix]
  let seg_e := insert ⟨e, by omega⟩ {x : Fin (2 * e + k) | ↑x < e} 
  have hhh : ∑ i_1 ∈ {x : Fin (2 * e + k) | ↑x < e}, ωs i ^ (↑i_1 : ℕ) * (E ωs f p e).coeff ↑i_1 = 
        ∑ i_1 ∈ seg_e, ωs i ^ (↑i_1 : ℕ) * (E ωs f p e).coeff ↑i_1 - 
                ωs i ^ ↑e * (E ωs f p e).coeff ↑e := by
    simp [seg_e]
  have hhhr : ∑ x ∈ {x: Fin (2 * e + k) | ↑x < e + k }, ωs i ^ (↑x : ℕ) * (Q ωs f p e).coeff ↑x 
    =∑ x ∈ Finset.range (e + k), ωs i ^ x * (Q ωs f p e).coeff x := by
      apply Finset.sum_bij (i := fun a ha => a.val)
        <;> try aesop (config := {warnOnNonterminal := false}) (add safe (by omega))
      exists ⟨b, by omega⟩

  conv =>
    lhs
    congr 
    · rw [Finset.sum_ite_of_true (by aesop),
          Finset.sum_equiv (t := {x : Fin (2 * e + k) | ↑x < e })
            (g := fun j => f i * (ωs i ^ (↑j : ℕ) * (E ωs f p e).coeff ↑j))
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
              aesop 
                (add simp seg_e)
                (add safe (by omega))
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
               rw [natDegree_E_eq_of_lt h_ham] at hif 
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
      rw [Finset.sum_bij (g := fun x => -(ωs i ^ (↑x : ℕ) * (Q ωs f p e).coeff ↑x)) 
        (t := { x : Fin (2 * e + k)  | x < e + k }) (by {
        intro a ha 
        exact (⟨↑a - e, by omega⟩ : Fin (2 * e + k))
      }) (by {
        rintro ⟨a, ha⟩
        simp
        omega
      }) (by 
        aesop 
          (add safe (by omega))
          (add safe forward Fin.ext)
      ) (by {
        rintro ⟨b, hb⟩ hh
        exists ⟨b + e, by 
          aesop 
            (add safe (by omega))
        ⟩
        aesop
      }) (by simp)]
      rw [Finset.sum_neg_distrib]
      rw [hhhr]
      rw [←Polynomial.sum_eq_of_subset (p := Q ωs f p e) (fun j x => ωs i ^ j * x) (by simp) (by {
          intro x hx 
          simp 
          simp at hx 
          rw [←Polynomial.ite_le_natDegree_coeff _ _ inferInstance] at hx 
          split_ifs at hx with hif
          apply Nat.lt_of_lt_of_le hif
          trans 
          apply Nat.add_le_add_left (natDegree_Q_le_of_lt h_ham)
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
      rfl
    }
  rw [mul_sub_left_distrib]
  rw [←eval_Q_eq_mul_eval_E]
  ring_nf
  have h_lead :(E ωs f p e).coeff e = (E ωs f p e).leadingCoeff := by
    simp only [Polynomial.leadingCoeff]
    rw [natDegree_E_eq_of_lt h_ham]
  rw [h_lead]
  simp 

def solution_to_E (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨insert e ((Finset.range e).filter (fun x => liftF v x ≠ 0)), 
    fun i => if i = e then 1 else if i < e then liftF v i else 0, by 
      aesop (add safe forward BerlekampWelch.liftF_ne_0)
    ⟩⟩

@[simp]
lemma solution_to_E_coeff {e k : ℕ} {v : Fin (2 * e + k) → F} {i : ℕ}:
  (solution_to_E e k v).coeff i = if i = e then 1 else if i < e then liftF v i else 0 := rfl

@[simp]
lemma solution_to_natDegree_E {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_E e k v).natDegree = e := by
  simp [solution_to_E, Polynomial.natDegree, Polynomial.degree]
  rw [sup_eq_left.2 ] <;> try simp
  omega

def solution_to_Q (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨(Finset.range (e + k)).filter (fun x => liftF v (e + x) ≠ 0), 
    fun i => if i < e + k then liftF v (e + i) else 0, by {
      aesop (add safe (by omega))
    }⟩⟩

@[simp]
lemma solution_to_natDegree_Q_le {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_Q e k v).natDegree ≤ e + k - 1 := by
  simp [solution_to_Q, Polynomial.natDegree, Polynomial.degree]
  rw [WithBot.unbotD_le_iff] <;>
  aesop (add safe [(by omega)])

end

end

end BW

end BerlekampWelch
