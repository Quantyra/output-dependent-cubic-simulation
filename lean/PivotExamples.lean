import SectorSimulation.GaussianPivot
open SectorSimulation

def reducedIsIdentity {n : Nat} (J : BinaryMatrix n) : Bool :=
  match gaussianRowProgram J with
  | none => false
  | some ops =>
    let R := (applyRowProgram ops J zeroVector).1
    (List.finRange n).all fun i => (List.finRange n).all fun k => R i k == decide (i = k)

def programRefuses {n : Nat} (J : BinaryMatrix n) : Bool :=
  (gaussianRowProgram J).isNone

def identity3 : BinaryMatrix 3 := fun i k => decide (i = k)
def swap3 : BinaryMatrix 3 := fun i k => decide ((i.val = 0 ∧ k.val = 1) ∨ (i.val = 1 ∧ k.val = 0) ∨ (i.val = 2 ∧ k.val = 2))
def dense3 : BinaryMatrix 3 := fun i k => decide ((i.val = 0 ∧ (k.val = 0 ∨ k.val = 1)) ∨ (i.val = 1 ∧ (k.val = 1 ∨ k.val = 2)) ∨ (i.val = 2 ∧ k.val = 2))
def singular3 : BinaryMatrix 3 := fun i k => decide (i.val = 0 ∧ k.val = 0)

#guard reducedIsIdentity (n := 0) (fun i _ => Fin.elim0 i)
#guard reducedIsIdentity identity3
#guard reducedIsIdentity swap3
#guard reducedIsIdentity dense3
#guard programRefuses singular3
