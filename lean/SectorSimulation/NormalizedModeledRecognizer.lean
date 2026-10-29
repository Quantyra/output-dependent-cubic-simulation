import SectorSimulation.ValidatedRawNormalization
import SectorSimulation.ModeledSourceRecognizer
namespace SectorSimulation

/-- Validate before normalization and require the decoded phase lists to be canonical.
    Full canonical JSON-byte matching remains a separate obligation. -/
def recognizeNormalizedModeledSource (gates : List NativeGate) :
    Option (Σ n, CircuitDescriptor n × List (RowOperation n)) := do
  let (raw, _) ← decodeHeaderDescriptor gates
  let canonical ← normalizeAfterRawValidation raw
  if raw = canonical then recognizeModeledSource gates else none

theorem recognizeNormalizedModeledSource_sound (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeNormalizedModeledSource gates = some ⟨n, (d, ops)⟩) :
    ∃ raw body, decodeHeaderDescriptor gates = some (raw, body) ∧
      normalizeAfterRawValidation raw = some raw ∧
      recognizeModeledSource gates = some ⟨n, (d, ops)⟩ := by
  unfold recognizeNormalizedModeledSource at h
  cases hd : decodeHeaderDescriptor gates with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨raw, body⟩
    cases hv : normalizeAfterRawValidation raw with
    | none => simp [hd, hv] at h
    | some canonical =>
      by_cases hc : raw = canonical
      · subst canonical
        simp [hd, hv] at h
        exact ⟨raw, body, rfl, hv, h⟩
      · simp [hd, hv, hc] at h

theorem recognizeNormalizedModeledSource_complete (gates : List NativeGate) (raw : RawTwoPhaseDescriptor)
    (body : List NativeGate) (n : Nat) (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hd : decodeHeaderDescriptor gates = some (raw, body))
    (hv : normalizeAfterRawValidation raw = some raw)
    (hr : recognizeModeledSource gates = some ⟨n, (d, ops)⟩) :
    recognizeNormalizedModeledSource gates = some ⟨n, (d, ops)⟩ := by
  simp [recognizeNormalizedModeledSource, hd, hv, hr]

theorem recognizeNormalizedModeledSource_replay (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeNormalizedModeledSource gates = some ⟨n, (d, ops)⟩) (state : SharedDyadicState n) :
    ∃ result j q, replayExactNative n gates state = some result ∧
      (∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x) ∧
      sourceOutputDerivativePivot d = some (j, q) ∧ matrixApply d.pairing j = outputUnit d ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  obtain ⟨_, _, _, _, hr⟩ := recognizeNormalizedModeledSource_sound gates n d ops h
  exact recognizeModeledSource_replay gates n d ops hr state

end SectorSimulation
