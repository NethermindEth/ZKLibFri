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

def FriVerifier (r : ℕ) : OracleComp
