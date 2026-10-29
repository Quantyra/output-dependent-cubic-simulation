import SectorSimulation.ValidatedHeaderReplay
namespace SectorSimulation

def recognizeModeledSource (gates : List NativeGate) : Option (Σ n, CircuitDescriptor n × List (RowOperation n)) := do
  let (⟨n, descriptor⟩, body) ← decodeValidatedHeader gates
  let ops ← gaussianRowProgram descriptor.pairing
  let expected ← compileModeledSourceBody descriptor ops
  if body = expected then some ⟨n, (descriptor, ops)⟩ else none

theorem recognizeModeledSource_sound (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeModeledSource gates = some ⟨n, (d, ops)⟩) :
    ∃ body, decodeValidatedHeader gates = some (⟨n, d⟩, body) ∧
      gaussianRowProgram d.pairing = some ops ∧ compileModeledSourceBody d ops = some body := by
  unfold recognizeModeledSource at h
  cases hd : decodeValidatedHeader gates with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨⟨k, candidate⟩, body⟩
    cases hp : gaussianRowProgram candidate.pairing with
    | none => simp [hd, hp] at h
    | some program =>
      cases hc : compileModeledSourceBody candidate program with
      | none => simp [hd, hp, hc] at h
      | some expected =>
        by_cases he : body = expected
        · simp [hd, hp, hc, he] at h
          obtain ⟨hk, hv⟩ := h
          subst k
          cases hv
          subst body
          exact ⟨expected, rfl, hp, hc⟩
        · simp [hd, hp, hc, he] at h

theorem recognizeModeledSource_replay (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (h : recognizeModeledSource gates = some ⟨n, (d, ops)⟩) (state : SharedDyadicState n) :
    ∃ result j q, replayExactNative n gates state = some result ∧
      (∀ x, sharedAmplitude result x = sharedAmplitude (modeledSourceBody d ops state) x) ∧
      sourceOutputDerivativePivot d = some (j, q) ∧ matrixApply d.pairing j = outputUnit d ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  obtain ⟨body, hd, hp, hc⟩ := recognizeModeledSource_sound gates n d ops h
  exact decodedValidatedHeader_replay_and_derivative gates body n d ops hd hc hp state

end SectorSimulation
