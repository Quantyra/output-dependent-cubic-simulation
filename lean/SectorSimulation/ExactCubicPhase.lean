import SectorSimulation.ExactControlledPhase
import SectorSimulation.CubicPhaseInteger
namespace SectorSimulation

def sharedToffoli {n : Nat} (a b target : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => state.numerator (applyToffoli a b target x), state.exponent⟩

def sharedCubicSign {n : Nat} (a b target : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if x a && x b && x target then cycloNeg (state.numerator x) else state.numerator x,
    state.exponent⟩

theorem sharedHToffoliH_numerator {n : Nat} (a b target : Fin n)
    (ha : a ≠ target) (hb : b ≠ target)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (sharedHadamard target (sharedToffoli a b target (sharedHadamard target state))).numerator x =
      cycloScale 4 (if x a && x b && x target then cycloNeg (state.numerator x) else state.numerator x) := by
  have hflip : flipWire target x target = !(x target) := by simp [flipWire]
  have ha' : flipWire target x a = x a := by simp [flipWire, ha]
  have hb' : flipWire target x b = x b := by simp [flipWire, hb]
  simp only [sharedHadamard, sharedToffoli, cycloHadamardNumerator, applyToffoli]
  cases hca : x a <;> cases hcb : x b <;> cases ht : x target <;>
    simp only [ha', hb', hflip, flipWire_involutive, hca, hcb, ht,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.false_and, Bool.true_and,
      if_true, if_false] <;>
    cases h1 : state.numerator x <;> cases h2 : state.numerator (flipWire target x) <;>
    simp only [cycloMul, cycloSqrtTwo, cycloAdd, cycloSub, cycloNeg, cycloScale, Cyclo8.mk.injEq] <;> omega

theorem sharedHToffoliH_cubic_sign {n : Nat} (a b target : Fin n)
    (ha : a ≠ target) (hb : b ≠ target)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard target (sharedToffoli a b target (sharedHadamard target state))) x =
      sharedAmplitude (sharedCubicSign a b target state) x := by
  apply Quotient.sound
  change dyadicEquivalent
    ⟨(sharedHadamard target (sharedToffoli a b target (sharedHadamard target state))).numerator x,
      (state.exponent+1)+1⟩
    ⟨(sharedCubicSign a b target state).numerator x, state.exponent⟩
  unfold dyadicEquivalent
  simp only [sharedHToffoliH_numerator a b target ha hb state x, sharedCubicSign, cycloScale_mul, Int.pow_add]
  congr 1
  omega

end SectorSimulation
