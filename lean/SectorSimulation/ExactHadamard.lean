import SectorSimulation.DyadicQuotient
namespace SectorSimulation

/-- Shared-denominator exact state, with all amplitudes divided by 2^exponent. -/
structure SharedDyadicState (n : Nat) where
  numerator : BinaryVector n → Cyclo8
  exponent : Nat

def cycloHadamardNumerator {n : Nat} (wire : Fin n)
    (state : BinaryVector n → Cyclo8) : BinaryVector n → Cyclo8 :=
  fun x => if x wire then cycloSub (state (flipWire wire x)) (state x)
    else cycloAdd (state x) (state (flipWire wire x))

def sharedHadamard {n : Nat} (wire : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => cycloMul cycloSqrtTwo (cycloHadamardNumerator wire state.numerator x),
    state.exponent + 1⟩

def sharedAmplitude {n : Nat} (state : SharedDyadicState n) (x : BinaryVector n) : ExactAmplitude :=
  exactOfDyadic ⟨state.numerator x, state.exponent⟩

/-- Two exact Hadamard numerator steps multiply each numerator by four. -/
theorem sharedHadamard_numerator_squared {n : Nat} (wire : Fin n)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (sharedHadamard wire (sharedHadamard wire state)).numerator x = cycloScale 4 (state.numerator x) := by
  have hf : flipWire wire x wire = !(x wire) := by simp [flipWire]
  simp only [sharedHadamard, cycloHadamardNumerator]
  cases hx : x wire <;>
    simp only [hx, hf, flipWire_involutive, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_true, if_false] <;>
    cases h1 : state.numerator x <;> cases h2 : state.numerator (flipWire wire x) <;>
    simp only [cycloMul, cycloSqrtTwo, cycloAdd, cycloSub, cycloScale, Cyclo8.mk.injEq] <;> omega

/-- Two normalized exact Hadamards restore every quotient-valued amplitude. -/
theorem sharedHadamard_squared {n : Nat} (wire : Fin n)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard wire (sharedHadamard wire state)) x = sharedAmplitude state x := by
  apply Quotient.sound
  change dyadicEquivalent ⟨(sharedHadamard wire (sharedHadamard wire state)).numerator x,
      (state.exponent + 1) + 1⟩ ⟨state.numerator x, state.exponent⟩
  unfold dyadicEquivalent
  simp only [sharedHadamard_numerator_squared, cycloScale_mul, Int.pow_add]
  congr 1
  omega

end SectorSimulation
