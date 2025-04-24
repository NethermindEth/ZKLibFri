import VCVio

import ZKLib.ProofSystem.Fri.RoundConsistency

section Defs

variable (F : Type) [Field F] 
variable (D : Subgroup Fˣ) 
variable (r : ℕ)

def FriCommitSpec : OracleSpec Unit := 
  fun _ ↦ (Unit, D)

inductive Oracle where
  | RO 
  | PO : (Fin r) -> Oracle

def FriQuerySpec : OracleSpec (Oracle r) := 
  fun i ↦ match i with
  | .RO => (Unit, D)
  | .PO _ => (F, F)
 
end Defs

variable {F : Type} [NonBinaryField F]
variable {D : Subgroup Fˣ} 
variable (r : ℕ) [NeZero r]

def getChallenge : (OracleComp (FriCommitSpec F D)) D 
  := OracleComp.lift (OracleSpec.query (spec := FriCommitSpec F D) () ())

noncomputable def commit_aux (f : Polynomial F) 
  : (OracleComp (FriCommitSpec F D)) (Polynomial F × List (Polynomial F)) := 
  List.foldlM (fun (f, acc) i => do
    let nextf <- (if i < r then do
      let α <- getChallenge;
      let α := α ^ i;
      let nextf := foldα f α.val
      return nextf
    else do
      return f)
    return (nextf, List.cons nextf acc)
  ) (f, []) (List.range r) 

noncomputable def commit (f : Polynomial F) 
  : (OracleComp (FriCommitSpec F D)) (List (Polynomial F)) := 
  Prod.snd <$> (commit_aux r f)

def getEval (i : ℕ) (x : F) 
  : (OracleComp (FriQuerySpec F D r)) F
  := OracleComp.lift  
    (OracleSpec.query (spec := FriQuerySpec F D r) (Oracle.PO <| Fin.ofNat' r i) x)

def getChallengeQ  :
    (OracleComp (FriQuerySpec F D r)) D :=
  OracleComp.lift 
    (OracleSpec.query (spec := FriQuerySpec F D r) Oracle.RO ())

noncomputable def query :
    OracleComp (FriQuerySpec F D r) Unit
  := 
  List.foldlM (fun _ i => do
    let x₀ <- getChallengeQ r
    -- todo
    return ()
  ) () (List.range r) 
