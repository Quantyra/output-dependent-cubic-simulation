import SectorSimulation.ExactHadamardProgram
namespace SectorSimulation

def modeledFourier {n : Nat} (ops : List (RowOperation n)) (state : SharedDyadicState n) : SharedDyadicState n :=
  runSharedCNOTs (rowProgramCNOTs ops).reverse (runSharedHadamards (List.finRange n) state)

theorem sharedCNOTs_amplitude {n : Nat} (gates : List (CNOTRecord n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (runSharedCNOTs gates state) x = sharedAmplitude state (runCNOTs gates.reverse x) := by
  simp [sharedAmplitude, runSharedCNOTs_numerator, runSharedCNOTs_exponent, runCNOTAmplitudes_apply]

theorem sharedCNOTs_amplitude_congr {n : Nat} (gates : List (CNOTRecord n))
    (a b : SharedDyadicState n) (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) (x : BinaryVector n) :
    sharedAmplitude (runSharedCNOTs gates a) x = sharedAmplitude (runSharedCNOTs gates b) x := by
  rw [sharedCNOTs_amplitude, sharedCNOTs_amplitude, h]

theorem modeledFourier_amplitude_congr {n : Nat} (ops : List (RowOperation n))
    (a b : SharedDyadicState n) (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) (x : BinaryVector n) :
    sharedAmplitude (modeledFourier ops a) x = sharedAmplitude (modeledFourier ops b) x := by
  apply sharedCNOTs_amplitude_congr
  exact runSharedHadamards_congr (List.finRange n) a b h

theorem exactNativeFourier_program {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hprog : gaussianRowProgram J = some ops) (state : SharedDyadicState n) :
    replayExactNative n (nativeFourierRecords ops) state = some (modeledFourier ops state) := by
  have hv : validCNOTs (rowProgramCNOTs ops).reverse := by
    intro g hg; exact rowProgramCNOTs_valid ops g (by simpa using hg)
  simp only [nativeFourierRecords, replayExactNative_append, exactNativeHadamardProgram]
  exact exactNativeCNOTProgram _ hv _

def sharedPhaseSign {n : Nat} (phase : PhaseANF n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if evalPhase phase x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩

theorem sharedPhaseSign_congr {n : Nat} (phase : PhaseANF n) (a b : SharedDyadicState n)
    (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) (x : BinaryVector n) :
    sharedAmplitude (sharedPhaseSign phase a) x = sharedAmplitude (sharedPhaseSign phase b) x := by
  cases hx : evalPhase phase x <;> simp [sharedAmplitude, sharedPhaseSign, hx] <;> try exact h x
  change exactNeg (sharedAmplitude a x) = exactNeg (sharedAmplitude b x)
  rw [h x]

def modeledSourceBody {n : Nat} (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (state : SharedDyadicState n) : SharedDyadicState n :=
  modeledFourier ops (sharedPhaseSign d.secondPhase
    (modeledFourier ops (sharedPhaseSign d.firstPhase (modeledFourier ops state))))

def sourcePhaseAnchor {n : Nat} (d : CircuitDescriptor n) : Fin n :=
  ⟨0, Nat.zero_lt_of_lt d.output.isLt⟩

def compileModeledSourceBody {n : Nat} (d : CircuitDescriptor n) (ops : List (RowOperation n)) : Option (List NativeGate) := do
  let first ← compilePhaseRecords (sourcePhaseAnchor d) d.firstPhase
  let second ← compilePhaseRecords (sourcePhaseAnchor d) d.secondPhase
  some (nativeFourierRecords ops ++ first ++ nativeFourierRecords ops ++ second ++ nativeFourierRecords ops)

theorem compileModeledSourceBody_correct {n : Nat} (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hprog : gaussianRowProgram d.pairing = some ops) (cubic : phasesAreCubic d = true)
    (state : SharedDyadicState n) :
    ∃ records result, compileModeledSourceBody d ops = some records ∧
      replayExactNative n records state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x := by
  have hd1 := phaseWithinDegree_sound d.firstPhase (Bool.and_eq_true_iff.mp cubic).1
  have hd2 := phaseWithinDegree_sound d.secondPhase (Bool.and_eq_true_iff.mp cubic).2
  let f0 := modeledFourier ops state
  obtain ⟨r0, p0, hc0, hr0, ha0⟩ := compilePhaseRecords_correct (sourcePhaseAnchor d) d.firstPhase hd1 f0
  let f1 := modeledFourier ops p0
  obtain ⟨r1, p1, hc1, hr1, ha1⟩ := compilePhaseRecords_correct (sourcePhaseAnchor d) d.secondPhase hd2 f1
  have e0 : ∀ x, sharedAmplitude p0 x = sharedAmplitude (sharedPhaseSign d.firstPhase f0) x := by
    intro x; simpa [sharedAmplitude, sharedPhaseSign] using ha0 x
  have e1 : ∀ x, sharedAmplitude f1 x = sharedAmplitude (modeledFourier ops (sharedPhaseSign d.firstPhase f0)) x :=
    modeledFourier_amplitude_congr ops p0 _ e0
  have e2 : ∀ x, sharedAmplitude p1 x = sharedAmplitude (sharedPhaseSign d.secondPhase
      (modeledFourier ops (sharedPhaseSign d.firstPhase f0))) x := by
    intro x
    have hh : sharedAmplitude p1 x = sharedAmplitude (sharedPhaseSign d.secondPhase f1) x := by
      simpa [sharedAmplitude, sharedPhaseSign] using ha1 x
    exact hh.trans (sharedPhaseSign_congr d.secondPhase f1 _ e1 x)
  refine ⟨nativeFourierRecords ops ++ r0 ++ nativeFourierRecords ops ++ r1 ++ nativeFourierRecords ops,
    modeledFourier ops p1, ?_, ?_, ?_⟩
  · simp [compileModeledSourceBody, hc0, hc1]
  · dsimp [f0] at hr0
    dsimp [f1] at hr1
    simp [replayExactNative_append, exactNativeFourier_program d.pairing ops hprog, hr0, hr1]
  · intro x
    exact modeledFourier_amplitude_congr ops p1 _ e2 x

end SectorSimulation
