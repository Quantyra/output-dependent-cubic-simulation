import SectorSimulation.HadamardInteger
namespace SectorSimulation

/-- Toffoli basis action: flip target exactly when both controls are set. -/
def applyToffoli {n : Nat} (a b target : Fin n) (x : BinaryVector n) : BinaryVector n :=
  if x a && x b then flipWire target x else x

def applyToffoliAmplitude {n : Nat} (a b target : Fin n)
    (state : BasisAmplitudes n Int) : BasisAmplitudes n Int :=
  fun x => state (applyToffoli a b target x)

/-- Unnormalized target-Hadamard conjugation gives a cubic controlled sign. -/
theorem hadamard_Toffoli_hadamard_numerator {n : Nat} (a b target : Fin n)
    (ha : a ≠ target) (hb : b ≠ target)
    (state : BasisAmplitudes n Int) (x : BinaryVector n) :
    hadamardNumerator target (applyToffoliAmplitude a b target
      (hadamardNumerator target state)) x =
      if x a && x b && x target then -(2 * state x) else 2 * state x := by
  have hflip : flipWire target x target = !(x target) := by simp [flipWire]
  have ha' : flipWire target x a = x a := by simp [flipWire, ha]
  have hb' : flipWire target x b = x b := by simp [flipWire, hb]
  simp only [hadamardNumerator, applyToffoliAmplitude, applyToffoli]
  cases hca : x a <;> cases hcb : x b <;> cases ht : x target <;>
    simp [ha', hb', hflip, flipWire_involutive, hca, hcb, ht] <;> omega

end SectorSimulation
