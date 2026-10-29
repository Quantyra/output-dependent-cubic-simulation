import SectorSimulation.ExactHadamard
namespace SectorSimulation

def sharedCNOT {n : Nat} (control target : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => state.numerator (applyCNOT control target x), state.exponent⟩

/-- The normalized H-CNOT-H numerator is four times the controlled-sign numerator. -/
theorem sharedHCXH_numerator {n : Nat} (control target : Fin n) (hct : control ≠ target)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (sharedHadamard target (sharedCNOT control target (sharedHadamard target state))).numerator x =
      cycloScale 4 (if x control && x target then cycloNeg (state.numerator x) else state.numerator x) := by
  have hflip : flipWire target x target = !(x target) := by simp [flipWire]
  have hcontrol : flipWire target x control = x control := by simp [flipWire, hct]
  have hcnot : applyCNOT control target x = (if x control then flipWire target x else x) := by
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
  simp only [sharedHadamard, sharedCNOT, cycloHadamardNumerator]
  cases hc : x control <;> cases ht : x target <;>
    simp only [hcnot, hcnotFlip, hflip, flipWire_involutive, hc, ht,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.false_and, Bool.true_and,
      if_true, if_false] <;>
    cases h1 : state.numerator x <;> cases h2 : state.numerator (flipWire target x) <;>
    simp only [cycloMul, cycloSqrtTwo, cycloAdd, cycloSub, cycloNeg, cycloScale, Cyclo8.mk.injEq] <;> omega

def sharedControlledSign {n : Nat} (control target : Fin n)
    (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if x control && x target then cycloNeg (state.numerator x) else state.numerator x,
    state.exponent⟩

theorem sharedHCXH_controlled_sign {n : Nat} (control target : Fin n) (hct : control ≠ target)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard target (sharedCNOT control target (sharedHadamard target state))) x =
      sharedAmplitude (sharedControlledSign control target state) x := by
  apply Quotient.sound
  change dyadicEquivalent
    ⟨(sharedHadamard target (sharedCNOT control target (sharedHadamard target state))).numerator x,
      (state.exponent+1)+1⟩
    ⟨(sharedControlledSign control target state).numerator x, state.exponent⟩
  unfold dyadicEquivalent
  simp only [sharedHCXH_numerator control target hct state x, sharedControlledSign, cycloScale_mul, Int.pow_add]
  congr 1
  omega

end SectorSimulation
