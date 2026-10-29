import SectorSimulation.SupportShapes
import SectorSimulation.MonomialDifference

/-!
An explicit degree-at-most-two term-list representation. This is an auxiliary
construction language; its translation into the source's bit-mask ANF and the
general cubic derivative construction remain to be proved.
-/

namespace SectorSimulation

inductive QuadraticTerm (n : Nat) where
  | constant
  | linear (i : Fin n)
  | product (i k : Fin n)

def evalQuadraticTerm {n : Nat} (term : QuadraticTerm n) (x : BinaryVector n) : Bool :=
  match term with
  | .constant => true
  | .linear i => x i
  | .product i k => x i && x k

def evalQuadraticTerms {n : Nat} : List (QuadraticTerm n) → BinaryVector n → Bool
  | [], _ => false
  | term :: rest, x => Bool.xor (evalQuadraticTerm term x) (evalQuadraticTerms rest x)

theorem evalQuadraticTerms_append {n : Nat} (p q : List (QuadraticTerm n))
    (x : BinaryVector n) :
    evalQuadraticTerms (p ++ q) x =
      Bool.xor (evalQuadraticTerms p x) (evalQuadraticTerms q x) := by
  induction p with
  | nil => simp [evalQuadraticTerms]
  | cons term rest ih => simp [evalQuadraticTerms, ih]

def conditionalQuadraticTerm {n : Nat} (coefficient : Bool)
    (term : QuadraticTerm n) : List (QuadraticTerm n) :=
  if coefficient then [term] else []

theorem evalConditionalQuadraticTerm {n : Nat} (coefficient : Bool)
    (term : QuadraticTerm n) (x : BinaryVector n) :
    evalQuadraticTerms (conditionalQuadraticTerm coefficient term) x =
      (coefficient && evalQuadraticTerm term x) := by
  cases coefficient <;> simp [conditionalQuadraticTerm, evalQuadraticTerms]

/-- The derivative of one coordinate is a constant controlled by the shift. -/
def linearDerivativeTerms {n : Nat} (i : Fin n) (j : BinaryVector n) :
    List (QuadraticTerm n) :=
  conditionalQuadraticTerm (j i) .constant

theorem evalLinearDerivativeTerms {n : Nat} (i : Fin n) (j x : BinaryVector n) :
    evalQuadraticTerms (linearDerivativeTerms i j) x =
      booleanDerivative (fun v => v i) (binaryShift j) x := by
  rw [binaryVariable_derivative]
  simp [linearDerivativeTerms, evalConditionalQuadraticTerm, evalQuadraticTerm]

/-- Construct the linear and constant derivative terms for two coordinates. -/
def quadraticDerivativeTerms {n : Nat} (i k : Fin n) (j : BinaryVector n) :
    List (QuadraticTerm n) :=
  conditionalQuadraticTerm (j i) (.linear k) ++
  conditionalQuadraticTerm (j k) (.linear i) ++
  conditionalQuadraticTerm (j i && j k) .constant

theorem evalQuadraticDerivativeTerms {n : Nat} (i k : Fin n) (j x : BinaryVector n) :
    evalQuadraticTerms (quadraticDerivativeTerms i k j) x =
      booleanDerivative (fun v => v i && v k) (binaryShift j) x := by
  rw [quadraticVariable_derivative]
  simp only [quadraticDerivativeTerms, evalQuadraticTerms_append,
    evalConditionalQuadraticTerm, evalQuadraticTerm]
  cases hi : x i <;> cases hk : x k <;> cases hji : j i <;> cases hjk : j k <;>
    simp

/-- Construct the quadratic derivative terms for a three-coordinate product. -/
def cubicDerivativeTerms {n : Nat} (i k l : Fin n) (j : BinaryVector n) :
    List (QuadraticTerm n) :=
  conditionalQuadraticTerm (j i) (.product k l) ++
  conditionalQuadraticTerm (j k) (.product i l) ++
  conditionalQuadraticTerm (j l) (.product i k) ++
  conditionalQuadraticTerm (j i && j k) (.linear l) ++
  conditionalQuadraticTerm (j i && j l) (.linear k) ++
  conditionalQuadraticTerm (j k && j l) (.linear i) ++
  conditionalQuadraticTerm (j i && j k && j l) .constant

/-- The constructed term list evaluates to the actual cubic-coordinate derivative. -/
theorem evalCubicDerivativeTerms {n : Nat} (i k l : Fin n) (j x : BinaryVector n) :
    evalQuadraticTerms (cubicDerivativeTerms i k l j) x =
      booleanDerivative (fun v => v i && v k && v l) (binaryShift j) x := by
  rw [cubicVariable_derivative]
  simp only [cubicDerivativeTerms, evalQuadraticTerms_append,
    evalConditionalQuadraticTerm, evalQuadraticTerm]
  cases hi : x i <;> cases hk : x k <;> cases hl : x l <;>
    cases hji : j i <;> cases hjk : j k <;> cases hjl : j l <;>
    simp

end SectorSimulation
