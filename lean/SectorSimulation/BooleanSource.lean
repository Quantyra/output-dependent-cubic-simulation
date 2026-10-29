import SectorSimulation.BinaryShift

/-!
Finite Boolean ANF source data for the literal circuit interface.

This module provides representations and evaluation functions only. It does
not yet prove correspondence with the Python encoder, native-gate replay,
matrix semantics, invertibility, polynomial degree reduction, or a paper theorem.
-/

namespace SectorSimulation

abbrev BinaryVector (n : Nat) := Fin n → Bool
abbrev Monomial (n : Nat) := Fin n → Bool
abbrev PhaseANF (n : Nat) := List (Monomial n)
abbrev BinaryMatrix (n : Nat) := Fin n → Fin n → Bool

/-- A monomial is a bit mask: selected variables contribute their values.
The empty mask evaluates to `true`, representing the constant monomial. -/
def evalMonomial {n : Nat} (m : Monomial n) (x : BinaryVector n) : Bool :=
  (List.finRange n).all fun i => !(m i) || x i

/-- A list of monomial masks denotes their sum over the two-element field.
Repeated masks cancel by XOR; lower and constant terms are retained. -/
def evalPhase {n : Nat} (p : PhaseANF n) (x : BinaryVector n) : Bool :=
  p.foldl (fun acc m => Bool.xor acc (evalMonomial m x)) false

def monomialDegree {n : Nat} (m : Monomial n) : Nat :=
  ((List.finRange n).filter fun i => m i).length

def phaseWithinDegree {n : Nat} (bound : Nat) (p : PhaseANF n) : Bool :=
  p.all fun m => monomialDegree m ≤ bound

/-- Matrix-vector multiplication over F2, with rows indexed first. -/
def matrixApply {n : Nat} (J : BinaryMatrix n) (x : BinaryVector n) : BinaryVector n :=
  fun i => (List.finRange n).foldl (fun acc j => Bool.xor acc (J i j && x j)) false

structure CircuitDescriptor (n : Nat) where
  pairing : BinaryMatrix n
  firstPhase : PhaseANF n
  secondPhase : PhaseANF n
  input : BinaryVector n
  output : Fin n

/-- The visible finite degree check; symmetry and invertibility are separate
obligations, not silently supplied by this check. -/
def phasesAreCubic {n : Nat} (d : CircuitDescriptor n) : Bool :=
  phaseWithinDegree 3 d.firstPhase && phaseWithinDegree 3 d.secondPhase

theorem evalPhase_empty {n : Nat} (x : BinaryVector n) : evalPhase [] x = false := by
  rfl

theorem evalPhase_duplicate_cancel {n : Nat} (m : Monomial n) (x : BinaryVector n) :
    evalPhase [m, m] x = false := by
  cases h : evalMonomial m x <;> simp [evalPhase, h]

/-- The output derivative before connecting `j` to the computed `J⁻¹ e`. -/
def secondPhaseDerivative {n : Nat} (d : CircuitDescriptor n)
    (j v : BinaryVector n) : Bool :=
  booleanDerivative (evalPhase d.secondPhase) (binaryShift j) v

theorem secondPhaseDerivative_shift_invariant {n : Nat} (d : CircuitDescriptor n)
    (j v : BinaryVector n) :
    secondPhaseDerivative d j (binaryShift j v) = secondPhaseDerivative d j v := by
  exact binaryDerivative_shift_invariant (evalPhase d.secondPhase) j v

end SectorSimulation
