import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Fin.Basic

section

open Fin

variable {F : Type} [DecidableEq F]
variable {n : ℕ}

@[simp]
lemma hamming_dist_zero {f g : ℕ → F} :
  Δ₀(liftF' (n := 0) f, liftF' g) = 0 := by
  simp 
  funext x 
  exact Fin.elim0 x

lemma hamming_dist_succ {f g : ℕ → F} :
  Δ₀(liftF' (n := n.succ) f, liftF' g) =
    Δ₀(liftF' (n := n) f, liftF' g) + if f n = g n then 0 else 1 := by
  simp [hammingDist]
  rw [Finset.card_bij
      (t := ({i : Fin n.succ | ¬ f i = g i ∧ ↑i < n} : Finset (Fin n.succ))) 
      (i := fun a _ ↦ Fin.castSucc a)
      (by aesop)
      (by aesop)
      (by {
        rintro ⟨b, hfin⟩ hb
        simp at hb
        exists ⟨b, by aesop⟩
        aesop
      })
  ]
  split_ifs with hif <;> simp [liftF']
  · exact Finset.card_bij
          (i := fun a _ ↦ a)
          (by {
            rintro ⟨a, hfin⟩ ha
            have hn : a ≠ n := by aesop
            aesop (add safe (by omega))
          })
          (by aesop)
          (by {
            rintro ⟨b, hfin⟩ hb
            have hn : b ≠ n := by aesop (add simp liftF')
            exists ⟨b, by omega⟩
            aesop 
          })
  · rw [Finset.card_bij
      (s := ({i | ¬ f i = g i } : Finset (Fin _)))
      (t := (insert (Fin.last n) ({i | ¬ f i = g i ∧ ↑i < n} : Finset (Fin _))))
      (i := fun a _ ↦ a)
      (by {
        rintro ⟨a, ha⟩ 
        aesop 
          (add safe (by omega))
          (add simp Fin.last)
      })
      (by aesop)
      (by {
        rintro ⟨b, hfin⟩ hb
        exists ⟨b, by trivial⟩
        simp
        simp at hb
        aesop (add simp Fin.last)
      })]
    simp

lemma hamming_dist_eq_fold {f g : ℕ → F} : 
  List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      0 (List.range n) 
  = Δ₀(liftF' (n := n) f, liftF' g) := by
  revert f g   
  induction' n with n ih
   <;> aesop (add simp [List.range_succ, hamming_dist_succ])  

private lemma fold_of_liftF_eq_fold {a : ℕ} [Zero F] {f g : Fin n → F} :
  List.foldl 
    (fun acc i => if liftF f i = liftF g i then acc else acc + 1) 
      a (List.range n) 
  =
  List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      a (List.finRange n) := by
  revert f g a 
  induction' n with n ih
  · simp 
  · intro a f g  
    simp only [List.range_succ_eq_map, List.foldl_cons, zero_add]
    split_ifs with hif <;> simp [List.finRange_succ]
    · simp [liftF] at hif
      simp [hif, List.foldl_map]
      have h_rhs : 
        List.foldl 
          (fun x y ↦ if f y.succ = g y.succ then x else x + 1) 
          a (List.finRange n)
        = 
        List.foldl 
          (fun x y ↦ if (f ∘ Fin.succ) y = (g ∘ Fin.succ) y then x else x + 1) 
          a (List.finRange n) := by congr
      rw [h_rhs, ←ih]
      aesop (add simp [Function.comp, liftF])
    · simp [liftF] at hif
      simp [hif, List.foldl_map]
      have h_rhs : 
        List.foldl 
          (fun x y ↦ if f y.succ = g y.succ then x else x + 1) 
          a.succ (List.finRange n)
        = 
        List.foldl 
          (fun x y ↦ if (f ∘ Fin.succ) y = (g ∘ Fin.succ) y then x else x + 1) 
          a.succ (List.finRange n) := by congr
      rw [h_rhs, ←ih]
      aesop (add simp [Function.comp, liftF])

lemma hamming_dist_eq_fold' [Zero F] {f g : Fin n → F} : 
  List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      0 (List.finRange n) 
  = Δ₀(f, g) := by
  rw [←fold_of_liftF_eq_fold,
    hamming_dist_eq_fold,
    Fin.liftF'_liftF,
    Fin.liftF'_liftF]

def instDecHammingLE [Zero F] {f g : Fin n → F} {e : ℕ} : 
    Decidable (Δ₀(f, g) ≤ e) := 
  if h : List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      0 (List.finRange n) ≤ e 
  then isTrue (by aesop (add simp hamming_dist_eq_fold'))
  else isFalse (by aesop (add simp hamming_dist_eq_fold'))

lemma an_implication_of_min_dist {k : ℕ} [Field F] {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj: Function.Injective ωs) 
  (h_dist : Δ₀((fun a ↦ Polynomial.eval a p) ∘ ωs, 0) < n - k + 1)
  : p = 0 := by
  by_cases hk : k = 0
  · simp [hk] at h_deg
  · have h_n_k_1 : n - k + 1 = n - (k - 1) := by omega
    rw [h_n_k_1] at h_dist 
    simp [hammingDist] at *
    rw [←Finset.compl_filter, Finset.card_compl] at h_dist
    simp at h_dist 
    have hk : 1 ≤ k := by omega
    rw [←Finset.card_image_of_injective _ h_inj 
    ] at h_dist
    have h_dist_p : k  ≤ 
      (@Finset.image (Fin n) F _ ωs {i | Polynomial.eval (ωs i) p = 0} : Finset F).card 
        := by omega
    by_cases heq_0 : p = 0 <;> try simp [heq_0]
    have h_dist := Nat.le_trans h_dist_p (by {
      apply Polynomial.card_le_degree_of_subset_roots (p := p)
      intro x hx 
      aesop
    })
    omega

lemma an_implication_of_min_dist' {k : ℕ} [Field F] {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj: Function.Injective ωs) 
  (h_dist : ‖(fun a ↦ Polynomial.eval a p) ∘ ωs‖₀ < n - k + 1)
  : p = 0 := an_implication_of_min_dist h_deg hn h_inj (by aesop)

end
