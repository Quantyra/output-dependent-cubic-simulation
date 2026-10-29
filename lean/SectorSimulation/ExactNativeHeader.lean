import SectorSimulation.ModeledFourier
namespace SectorSimulation

theorem sharedX_squared {n : Nat} (wire : Fin n) (state : SharedDyadicState n) :
    sharedX wire (sharedX wire state) = state := by
  cases state with | mk f e => simp [sharedX, flipWire_involutive]

theorem sharedZ_squared {n : Nat} (wire : Fin n) (state : SharedDyadicState n) :
    sharedZ wire (sharedZ wire state) = state := by
  cases state with | mk f e =>
    simp only [sharedZ]
    congr 1
    funext x
    cases hx : x wire <;> simp [hx, cycloNeg]

theorem exactNativeHeader_identity {n : Nat} (wire0 : Fin n) (h0 : wire0.val = 0)
    (bits : List Bool) (state : SharedDyadicState n) :
    replayExactNative n (encodeNativeHeader bits) state =
      some (sharedHadamard wire0 (sharedHadamard wire0 state)) := by
  induction bits generalizing state with
  | nil =>
    simpa [encodeNativeHeader, nativeH0, h0] using exactNative_HH wire0 state
  | cons bit rest ih =>
    cases bit
    · have hw : 0 < n := by simpa [h0] using wire0.isLt
      simpa [encodeNativeHeader, nativeX0, replayExactNative, applyExactNative, hw, h0, sharedX_squared] using ih state
    · have hw : 0 < n := by simpa [h0] using wire0.isLt
      simpa [encodeNativeHeader, nativeZ0, replayExactNative, applyExactNative, hw, h0, sharedZ_squared] using ih state

theorem exactNativeHeader_amplitudes {n : Nat} (wire0 : Fin n) (h0 : wire0.val = 0)
    (bits : List Bool) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (encodeNativeHeader bits) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude state x := by
  exact ⟨sharedHadamard wire0 (sharedHadamard wire0 state), exactNativeHeader_identity wire0 h0 bits state,
    sharedHadamard_squared wire0 state⟩

theorem modeledSourceBody_congr {n : Nat} (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (a b : SharedDyadicState n) (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) (x : BinaryVector n) :
    sharedAmplitude (modeledSourceBody d ops a) x = sharedAmplitude (modeledSourceBody d ops b) x := by
  apply modeledFourier_amplitude_congr
  intro y
  apply sharedPhaseSign_congr
  intro z
  apply modeledFourier_amplitude_congr
  intro v
  apply sharedPhaseSign_congr
  intro q
  exact modeledFourier_amplitude_congr ops a b h q

theorem exactNativeHeader_sourceBody {n : Nat} (wire0 : Fin n) (h0 : wire0.val = 0)
    (bits : List Bool) (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hprog : gaussianRowProgram d.pairing = some ops) (cubic : phasesAreCubic d = true)
    (state : SharedDyadicState n) :
    ∃ body result, compileModeledSourceBody d ops = some body ∧
      replayExactNative n (encodeNativeHeader bits ++ body) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x := by
  obtain ⟨mid, hm, he⟩ := exactNativeHeader_amplitudes wire0 h0 bits state
  obtain ⟨body, result, hc, hr, ha⟩ := compileModeledSourceBody_correct d ops hprog cubic mid
  refine ⟨body, result, hc, ?_, ?_⟩
  · simp only [replayExactNative_append, hm]; exact hr
  · intro x; exact (ha x).trans (modeledSourceBody_congr d ops mid state he x)

end SectorSimulation
