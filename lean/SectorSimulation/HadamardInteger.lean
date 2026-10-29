import SectorSimulation.PhaseGateAmplitude
namespace SectorSimulation

/-- Hadamard numerator on integer coefficient functions; normalization is not included. -/
def hadamardNumerator {n : Nat} (wire : Fin n)
    (state : BasisAmplitudes n Int) : BasisAmplitudes n Int :=
  fun x => if x wire then state (flipWire wire x) - state x else state x + state (flipWire wire x)

theorem hadamardNumerator_squared {n : Nat} (wire : Fin n)
    (state : BasisAmplitudes n Int) (x : BinaryVector n) :
    hadamardNumerator wire (hadamardNumerator wire state) x = 2 * state x := by
  have hf : flipWire wire x wire = !(x wire) := by simp [flipWire]
  simp only [hadamardNumerator]
  cases hx : x wire <;>
    simp [hf, flipWire_involutive, hx] <;> omega

/-- An unnormalized target Hadamard conjugates CNOT to a controlled sign. -/
theorem hadamard_CNOT_hadamard_numerator {n : Nat} (control target : Fin n)
    (hct : control ≠ target) (state : BasisAmplitudes n Int) (x : BinaryVector n) :
    hadamardNumerator target (applyCNOTAmplitude (control, target)
      (hadamardNumerator target state)) x =
      if x control && x target then -(2 * state x) else 2 * state x := by
  have hflip : flipWire target x target = !(x target) := by simp [flipWire]
  have hcontrol : flipWire target x control = x control := by
    simp [flipWire, hct]
  have hcnot : applyCNOT control target x =
      (if x control then flipWire target x else x) := by
    funext i
    by_cases hi : i = target
    · subst i
      cases hc : x control <;> cases ht : x target <;>
        simp [applyCNOT, vectorAddRow, flipWire, hc, ht]
    · cases hc : x control <;> simp [applyCNOT, vectorAddRow, flipWire, hi]
  have hcnotFlip : applyCNOT control target (flipWire target x) =
      (if x control then x else flipWire target x) := by
    funext i
    by_cases hi : i = target
    · subst i
      cases hc : x control <;> cases ht : x target <;>
        simp [applyCNOT, vectorAddRow, flipWire, hct, hc, ht]
    · cases hc : x control <;> simp [applyCNOT, vectorAddRow, flipWire, hi]
  simp only [hadamardNumerator, applyCNOTAmplitude]
  cases hc : x control <;> cases ht : x target <;>
    simp [hcnot, hcnotFlip, hflip, flipWire_involutive, hc, ht] <;> omega

end SectorSimulation
