import SectorSimulation.PhaseBlockCompiler
namespace SectorSimulation

theorem applyExactNative_zero (gate : NativeGate) (state : SharedDyadicState 0) :
    applyExactNative 0 gate state = none := by
  unfold applyExactNative
  repeat' split <;> simp_all

theorem replayExactNative_zero_nonempty (gate : NativeGate) (rest : List NativeGate)
    (state : SharedDyadicState 0) : replayExactNative 0 (gate :: rest) state = none := by
  simp [replayExactNative, applyExactNative_zero]

def zeroWireVector : BinaryVector 0 := fun i => Fin.elim0 i

def zeroWireOne : SharedDyadicState 0 := ⟨fun _ => cycloOne, 0⟩

theorem zeroWireOne_not_negative :
    sharedAmplitude zeroWireOne zeroWireVector ≠ sharedAmplitude (sharedNeg zeroWireOne) zeroWireVector := by
  intro h
  have he := Quotient.exact h
  change dyadicEquivalent ⟨cycloOne, 0⟩ ⟨cycloNeg cycloOne, 0⟩ at he
  simp [dyadicEquivalent, cycloScale, cycloOne, cycloNeg] at he

theorem noZeroWireNativeConstantSign :
    ¬ ∃ records result, replayExactNative 0 records zeroWireOne = some result ∧
      sharedAmplitude result zeroWireVector = sharedAmplitude (sharedNeg zeroWireOne) zeroWireVector := by
  intro h
  obtain ⟨records, result, hr, ha⟩ := h
  cases records with
  | nil =>
    simp [replayExactNative] at hr
    subst result
    exact zeroWireOne_not_negative ha
  | cons gate rest =>
    rw [replayExactNative_zero_nonempty] at hr
    cases hr

end SectorSimulation
