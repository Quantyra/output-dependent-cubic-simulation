import SectorSimulation.NormalizedModeledRecognizer
import SectorSimulation.DescriptorJsonEncode
namespace SectorSimulation

/-- Compact Lean JSON rendering; correspondence to Python is not assumed. -/
def canonicalDescriptorBytes (raw : RawTwoPhaseDescriptor) : List Nat :=
  (rawDescriptorJson raw).compress.toUTF8.data.toList.map UInt8.toNat

def recognizeByteCanonicalModeledSource (gates : List NativeGate) :
    Option (Σ n, CircuitDescriptor n × List (RowOperation n)) := do
  let (bytes, _) ← decodeNumericHeader gates
  let (raw, _) ← decodeHeaderDescriptor gates
  if bytes.map Fin.val = canonicalDescriptorBytes raw then
    recognizeNormalizedModeledSource gates
  else none

theorem recognizeByteCanonical_sound (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeByteCanonicalModeledSource gates = some ⟨n, (d, ops)⟩) :
    ∃ bytes raw body suffix, decodeNumericHeader gates = some (bytes, body) ∧
      decodeHeaderDescriptor gates = some (raw, suffix) ∧
      bytes.map Fin.val = canonicalDescriptorBytes raw ∧
      recognizeNormalizedModeledSource gates = some ⟨n, (d, ops)⟩ := by
  unfold recognizeByteCanonicalModeledSource at h
  cases hb : decodeNumericHeader gates with
  | none => simp [hb] at h
  | some p =>
    rcases p with ⟨bytes, body⟩
    cases hd : decodeHeaderDescriptor gates with
    | none => simp [hb, hd] at h
    | some q =>
      rcases q with ⟨raw, suffix⟩
      by_cases he : bytes.map Fin.val = canonicalDescriptorBytes raw
      · simp [hb, hd, he] at h
        exact ⟨bytes, raw, body, suffix, rfl, rfl, he, h⟩
      · simp [hb, hd, he] at h

theorem recognizeByteCanonical_complete (gates : List NativeGate) (bytes : List (Fin 256))
    (raw : RawTwoPhaseDescriptor) (body suffix : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hb : decodeNumericHeader gates = some (bytes, body))
    (hd : decodeHeaderDescriptor gates = some (raw, suffix))
    (he : bytes.map Fin.val = canonicalDescriptorBytes raw)
    (hr : recognizeNormalizedModeledSource gates = some ⟨n, (d, ops)⟩) :
    recognizeByteCanonicalModeledSource gates = some ⟨n, (d, ops)⟩ := by
  simp [recognizeByteCanonicalModeledSource, hb, hd, he, hr]

theorem recognizeByteCanonical_replay (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeByteCanonicalModeledSource gates = some ⟨n, (d, ops)⟩) (state : SharedDyadicState n) :
    ∃ result j q, replayExactNative n gates state = some result ∧
      (∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x) ∧
      sourceOutputDerivativePivot d = some (j, q) ∧ matrixApply d.pairing j = outputUnit d ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  obtain ⟨_, _, _, _, _, _, _, hr⟩ := recognizeByteCanonical_sound gates n d ops h
  exact recognizeNormalizedModeledSource_replay gates n d ops hr state

end SectorSimulation
