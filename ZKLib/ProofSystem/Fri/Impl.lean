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

variable {F : Type} [NonBinaryField F] [DecidableEq F]
variable {D : Subgroup Fˣ}

def getChallenge : (OracleComp (FriCommitSpec F D)) D
  := OracleComp.lift (OracleSpec.query () ())

noncomputable def commit_aux (r : ℕ) (f : Polynomial F)
  : (OracleComp (FriCommitSpec F D)) (Polynomial F × List (Polynomial F)) :=
  List.foldlM (fun (f, acc) i => do
    let nextf <- (do
      let α <- getChallenge;
      let α := α ^ i;
      let nextf := foldα f α.val
      return nextf)
    return (nextf, List.cons nextf acc)
  ) (f, []) (List.range (r - 1))

variable {r : ℕ} [NeZero r]

noncomputable def commit (f : Polynomial F)
  : (OracleComp (FriCommitSpec F D)) (List (Polynomial F)) :=
  Function.uncurry List.cons <$> (commit_aux r f)

def getEval (i : ℕ) (x : F)
  : (OracleComp (FriQuerySpec F D r)) F
  := OracleComp.lift
    (OracleSpec.query (Oracle.PO <| Fin.ofNat' r i) x)

def getChallengeQ  :
    (OracleComp (FriQuerySpec F D r)) D :=
  OracleComp.lift
    (OracleSpec.query Oracle.RO ())

noncomputable def query :
    OracleComp (FriQuerySpec F D r) Unit
  := do
    let challenges <- List.foldlM (fun acc _ => do
     let c <- getChallengeQ;
     return acc ++ [c.val.val]) [] (List.range r);
    List.foldlM (fun _ i => do
      let x₀ := challenges.getD i (0 : F);
      let s₀ <- getChallengeQ;
      let s₀ := s₀.val.val;
      let α₀ <- getEval i s₀;
      let α₁ <- getEval i (-s₀);
      let β <- getEval i.succ (s₀ ^ 2);
      guard (consistency_check x₀ s₀ (-s₀) α₀ α₁ β)
    ) () (List.range r)
