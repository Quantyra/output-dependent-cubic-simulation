import SectorSimulation.ExactNativeHeader
import SectorSimulation.NativeJsonDescriptor
namespace SectorSimulation

theorem decodedValidatedHeader_prefix (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (body : List NativeGate)
    (h : decodeValidatedHeader gates = some (⟨n, d⟩, body)) :
    ∃ bytes, gates = encodeNumericHeader bytes ++ body := by
  unfold decodeValidatedHeader at h
  cases hr : decodeHeaderDescriptor gates with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨raw, suffix⟩
    cases hv : rawDescriptorToValidated raw with
    | none => simp [hr, hv] at h
    | some result =>
      simp [hr, hv] at h
      have hb : suffix = body := h.2
      subst suffix
      exact decodedHeader_has_encoded_prefix gates raw body hr

theorem decodedValidatedHeader_sourceBody (gates body : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hdecode : decodeValidatedHeader gates = some (⟨n, d⟩, body))
    (hbody : compileModeledSourceBody d ops = some body)
    (hprog : gaussianRowProgram d.pairing = some ops) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n gates state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x := by
  have hv := decodeValidatedHeader_valid gates n d body hdecode
  have cubic : phasesAreCubic d = true := (sourceDescriptorValid_correct d).mp hv |>.1
  obtain ⟨bytes, hg⟩ := decodedValidatedHeader_prefix gates n d body hdecode
  have hn : 0 < n := circuitDescriptor_has_wire d
  let wire0 : Fin n := ⟨0, hn⟩
  obtain ⟨compiled, result, hc, hr, ha⟩ := exactNativeHeader_sourceBody wire0 rfl
    (headerBytesBits (bytes.map fun b => headerByteFromNat b.val)) d ops hprog cubic state
  rw [hbody] at hc
  have heq : body = compiled := Option.some.inj hc
  refine ⟨result, ?_, ha⟩
  rw [hg, heq]
  exact hr

theorem decodedValidatedHeader_replay_and_derivative (gates body : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hdecode : decodeValidatedHeader gates = some (⟨n, d⟩, body))
    (hbody : compileModeledSourceBody d ops = some body)
    (hprog : gaussianRowProgram d.pairing = some ops) (state : SharedDyadicState n) :
    ∃ result j q, replayExactNative n gates state = some result ∧
      (∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x) ∧
      sourceOutputDerivativePivot d = some (j, q) ∧ matrixApply d.pairing j = outputUnit d ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  obtain ⟨result, hr, ha⟩ := decodedValidatedHeader_sourceBody gates body n d ops hdecode hbody hprog state
  obtain ⟨j, q, hq, hj, _, _, hdeg, hlen, heval⟩ := decodedValidatedHeader_outputDerivative gates n d body hdecode
  exact ⟨result, j, q, hr, ha, hq, hj, hdeg, hlen, heval⟩

end SectorSimulation
