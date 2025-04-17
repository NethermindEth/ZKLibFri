import VCVio

import ZKLib.ProofSystem.Fri.RoundConsistency

def Transcript (F : Type) : Type := List F

def FriSpec (F : Type) (r : ℕ) : OracleSpec (Fin (r + 1)) := 
  fun i ↦ match i.val with
  -- FS oracle 
  | 0 => (Transcript F, F)
  -- PIOP oracle 
  | _ => (F, F)

def FriMonad (F : Type) (r : ℕ) := OracleComp (FriSpec F r)

def FriVerifierQueryAux (F : Type) (r : ℕ) (i : ℕ) := 
  match i with 
  | 0 =>  

/- def FriVerifierQuery (F : Type) (r : ℕ) : FriMonad F r  -/
