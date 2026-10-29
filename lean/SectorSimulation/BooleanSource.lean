import SectorSimulation.BinaryShift
import SectorSimulation.DerivativeLinear

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

/-- A bit-mask monomial is true exactly when all selected variables are true. -/
theorem evalMonomial_eq_true_iff {n : Nat} (m : Monomial n) (x : BinaryVector n) :
    evalMonomial m x = true ↔ ∀ i, m i = true → x i = true := by
  simp only [evalMonomial, List.all_eq_true]
  constructor
  · intro h i hi
    have selected := h i (List.mem_finRange i)
    simpa [hi] using selected
  · intro h i _
    cases hi : m i with
    | false => simp
    | true => simp [h i hi]

/-- The empty monomial mask is the multiplicative constant one. -/
theorem evalMonomial_emptyMask {n : Nat} (x : BinaryVector n) :
    evalMonomial (fun _ => false) x = true := by
  apply (evalMonomial_eq_true_iff (fun _ => false) x).2
  intro i impossible
  cases impossible

/-- Selected indices in canonical finite-vector order. -/
def selectedVariables {n : Nat} (m : Monomial n) : List (Fin n) :=
  (List.finRange n).filter fun i => m i

/-- Bit-mask evaluation agrees with the product over its selected indices. -/
theorem evalMonomial_selectedVariables {n : Nat} (m : Monomial n) (x : BinaryVector n) :
    evalMonomial m x = (selectedVariables m).all x := by
  apply Bool.eq_iff_iff.mpr
  change (evalMonomial m x = true ↔ (selectedVariables m).all x = true)
  rw [evalMonomial_eq_true_iff, List.all_eq_true]
  constructor
  · intro h i hi
    have selected : m i = true := (List.mem_filter.mp hi).2
    exact h i selected
  · intro h i hi
    exact h i (List.mem_filter.mpr ⟨List.mem_finRange i, hi⟩)

/-- A list of monomial masks denotes their sum over the two-element field.
Repeated masks cancel by XOR; lower and constant terms are retained. -/
def evalPhase {n : Nat} (p : PhaseANF n) (x : BinaryVector n) : Bool :=
  p.foldl (fun acc m => Bool.xor acc (evalMonomial m x)) false

def monomialDegree {n : Nat} (m : Monomial n) : Nat :=
  ((List.finRange n).filter fun i => m i).length

/-- The mask degree is exactly the length of its selected-index list. -/
theorem monomialDegree_eq_selectedLength {n : Nat} (m : Monomial n) :
    monomialDegree m = (selectedVariables m).length := by
  rfl

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

/-- Folding from an arbitrary initial bit translates the zero-initial fold. -/
theorem phaseFold_from {n : Nat} (p : PhaseANF n) (x : BinaryVector n) (initial : Bool) :
    p.foldl (fun acc m => Bool.xor acc (evalMonomial m x)) initial =
      Bool.xor initial (evalPhase p x) := by
  induction p generalizing initial with
  | nil => cases initial <;> rfl
  | cons m rest ih =>
    simp only [evalPhase, List.foldl_cons] at ih ⊢
    rw [ih (Bool.xor initial (evalMonomial m x)),
      ih (Bool.xor false (evalMonomial m x))]
    cases initial <;> cases h : evalMonomial m x <;>
      cases t : rest.foldl (fun acc m => Bool.xor acc (evalMonomial m x)) false <;>
      simp

/-- ANF concatenation evaluates as XOR, retaining duplicate cancellation. -/
theorem evalPhase_append {n : Nat} (p q : PhaseANF n) (x : BinaryVector n) :
    evalPhase (p ++ q) x = Bool.xor (evalPhase p x) (evalPhase q x) := by
  unfold evalPhase
  rw [List.foldl_append]
  exact phaseFold_from q x (p.foldl (fun acc m => Bool.xor acc (evalMonomial m x)) false)

/-- Differentiation distributes over the actual represented ANF concatenation. -/
theorem phaseDerivative_append {n : Nat} (p q : PhaseANF n)
    (shift : BinaryVector n → BinaryVector n) (x : BinaryVector n) :
    booleanDerivative (evalPhase (p ++ q)) shift x =
      Bool.xor (booleanDerivative (evalPhase p) shift x)
        (booleanDerivative (evalPhase q) shift x) := by
  have h : evalPhase (p ++ q) =
      fun v => Bool.xor (evalPhase p v) (evalPhase q v) := by
    funext v
    exact evalPhase_append p q v
  rw [h]
  exact booleanDerivative_xor (evalPhase p) (evalPhase q) shift x

/-- The output derivative before connecting `j` to the computed `J⁻¹ e`. -/
def secondPhaseDerivative {n : Nat} (d : CircuitDescriptor n)
    (j v : BinaryVector n) : Bool :=
  booleanDerivative (evalPhase d.secondPhase) (binaryShift j) v

theorem secondPhaseDerivative_shift_invariant {n : Nat} (d : CircuitDescriptor n)
    (j v : BinaryVector n) :
    secondPhaseDerivative d j (binaryShift j v) = secondPhaseDerivative d j v := by
  exact binaryDerivative_shift_invariant (evalPhase d.secondPhase) j v

end SectorSimulation
