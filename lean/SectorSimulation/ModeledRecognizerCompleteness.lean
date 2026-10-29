import SectorSimulation.ModeledSourceRecognizer
namespace SectorSimulation

theorem recognizeModeledSource_complete (gates body : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n))
    (hd : decodeValidatedHeader gates = some (⟨n, d⟩, body))
    (hp : gaussianRowProgram d.pairing = some ops)
    (hc : compileModeledSourceBody d ops = some body) :
    recognizeModeledSource gates = some ⟨n, (d, ops)⟩ := by
  simp [recognizeModeledSource, hd, hp, hc]

theorem recognizeModeledSource_iff (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (ops : List (RowOperation n)) :
    recognizeModeledSource gates = some ⟨n, (d, ops)⟩ ↔
      ∃ body, decodeValidatedHeader gates = some (⟨n, d⟩, body) ∧
        gaussianRowProgram d.pairing = some ops ∧ compileModeledSourceBody d ops = some body := by
  constructor
  · exact recognizeModeledSource_sound gates n d ops
  · intro h; obtain ⟨body, hd, hp, hc⟩ := h
    exact recognizeModeledSource_complete gates body n d ops hd hp hc

theorem encodedValidatedHeader_roundtrip (bytes : List (Fin 256)) (text : String)
    (json : Lean.Json) (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (body : List NativeGate) (ha : decodeAscii bytes = some text)
    (hj : (Lean.Json.parse text).toOption = some json) (he : extractTwoPhaseDescriptor json = some raw)
    (hv : rawDescriptorToValidated raw = some ⟨n, d⟩) :
    decodeValidatedHeader (encodeNumericHeader bytes ++ body) = some (⟨n, d⟩, body) := by
  simp [decodeValidatedHeader, decodeHeaderDescriptor, numeric_native_header_roundtrip, ha, hj, he, hv]

theorem encodedModeledSource_recognized (bytes : List (Fin 256)) (text : String)
    (json : Lean.Json) (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (ops : List (RowOperation n)) (body : List NativeGate)
    (ha : decodeAscii bytes = some text) (hj : (Lean.Json.parse text).toOption = some json)
    (he : extractTwoPhaseDescriptor json = some raw) (hv : rawDescriptorToValidated raw = some ⟨n, d⟩)
    (hp : gaussianRowProgram d.pairing = some ops) (hc : compileModeledSourceBody d ops = some body) :
    recognizeModeledSource (encodeNumericHeader bytes ++ body) = some ⟨n, (d, ops)⟩ := by
  exact recognizeModeledSource_complete _ body n d ops
    (encodedValidatedHeader_roundtrip bytes text json raw n d body ha hj he hv) hp hc

theorem validatedDescriptor_has_modeledBody {n : Nat} (d : CircuitDescriptor n)
    (valid : sourceDescriptorValid d = true) (state : SharedDyadicState n) :
    ∃ ops body, gaussianRowProgram d.pairing = some ops ∧ compileModeledSourceBody d ops = some body := by
  have hc : phasesAreCubic d = true := (sourceDescriptorValid_correct d).mp valid |>.1
  have hsome : (gaussianRowProgram d.pairing).isSome = true := by
    have hv := valid
    simp only [sourceDescriptorValid, Bool.and_eq_true] at hv
    exact hv.2
  obtain ⟨ops, hp⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨body, _, hb, _, _⟩ := compileModeledSourceBody_correct d ops hp hc state
  exact ⟨ops, body, hp, hb⟩

theorem encodedValidSource_has_recognizedBody (bytes : List (Fin 256)) (text : String)
    (json : Lean.Json) (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (ha : decodeAscii bytes = some text) (hj : (Lean.Json.parse text).toOption = some json)
    (he : extractTwoPhaseDescriptor json = some raw) (hv : rawDescriptorToValidated raw = some ⟨n, d⟩)
    (state : SharedDyadicState n) :
    ∃ ops body, recognizeModeledSource (encodeNumericHeader bytes ++ body) = some ⟨n, (d, ops)⟩ := by
  have valid := rawDescriptorToValidated_valid raw n d hv
  obtain ⟨ops, body, hp, hc⟩ := validatedDescriptor_has_modeledBody d valid state
  exact ⟨ops, body, encodedModeledSource_recognized bytes text json raw n d ops body ha hj he hv hp hc⟩

end SectorSimulation
