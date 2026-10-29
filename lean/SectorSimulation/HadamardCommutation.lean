import SectorSimulation.HadamardInteger
namespace SectorSimulation

/-- A sign depending only on other wires commutes with an unnormalized Hadamard. -/
def applyBooleanSign {n : Nat} (predicate : BinaryVector n → Bool)
    (state : BasisAmplitudes n Int) : BasisAmplitudes n Int :=
  fun x => if predicate x then -state x else state x

theorem hadamard_commutes_invariant_sign {n : Nat} (wire : Fin n)
    (predicate : BinaryVector n → Bool)
    (hinv : ∀ x, predicate (flipWire wire x) = predicate x)
    (state : BasisAmplitudes n Int) :
    hadamardNumerator wire (applyBooleanSign predicate state) =
      applyBooleanSign predicate (hadamardNumerator wire state) := by
  funext x
  simp only [hadamardNumerator, applyBooleanSign]
  rw [hinv x]
  cases hw : x wire <;> cases hp : predicate x <;> simp <;> omega

theorem cnot_flip_commute {n : Nat} (wire control target : Fin n)
    (hwc : wire ≠ control) (hwt : wire ≠ target) (x : BinaryVector n) :
    applyCNOT control target (flipWire wire x) = flipWire wire (applyCNOT control target x) := by
  funext i
  by_cases hiw : i = wire
  · subst i
    simp [applyCNOT, vectorAddRow, flipWire, hwt]
  · by_cases hit : i = target
    · subst i
      simp [applyCNOT, vectorAddRow, flipWire, Ne.symm hwt, Ne.symm hwc]
    · simp [applyCNOT, vectorAddRow, flipWire, hiw, hit]

theorem hadamard_commutes_disjoint_CNOT {n : Nat} (wire control target : Fin n)
    (hwc : wire ≠ control) (hwt : wire ≠ target)
    (state : BasisAmplitudes n Int) :
    hadamardNumerator wire (applyCNOTAmplitude (control,target) state) =
      applyCNOTAmplitude (control,target) (hadamardNumerator wire state) := by
  funext x
  have hw : applyCNOT control target x wire = x wire := by
    simp [applyCNOT, vectorAddRow, hwt]
  simp only [hadamardNumerator, applyCNOTAmplitude]
  rw [hw, cnot_flip_commute wire control target hwc hwt x]

end SectorSimulation
