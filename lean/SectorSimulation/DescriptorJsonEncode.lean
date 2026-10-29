import SectorSimulation.ModeledRecognizerCompleteness
namespace SectorSimulation

def jsonNat (n : Nat) : Lean.Json := Lean.Json.num (Lean.JsonNumber.fromNat n)
def jsonNatArray (xs : List Nat) : Lean.Json := Lean.Json.arr (xs.map jsonNat).toArray

def rawDescriptorJson (raw : RawTwoPhaseDescriptor) : Lean.Json :=
  Lean.Json.arr #[Lean.Json.str "cubic-field-v1", jsonNat raw.n, jsonNatArray raw.rows,
    Lean.Json.arr #[jsonNatArray raw.phase0, jsonNatArray raw.phase1],
    jsonNat raw.basis, jsonNat raw.output]

theorem jsonNat_getNat (n : Nat) : (jsonNat n).getNat?.toOption = some n := by
  rfl

theorem jsonNatArray_extract (xs : List Nat) : jsonNatList (jsonNatArray xs) = some xs := by
  change ((xs.map jsonNat).mapM (fun x => x.getNat?.toOption)) = some xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, jsonNat_getNat, ih]
    rfl

theorem jsonArr_get (xs : Array Lean.Json) : (Lean.Json.arr xs).getArr?.toOption = some xs := by rfl
theorem jsonStr_get (s : String) : (Lean.Json.str s).getStr?.toOption = some s := by rfl

theorem rawDescriptorJson_extract (raw : RawTwoPhaseDescriptor) :
    extractTwoPhaseDescriptor (rawDescriptorJson raw) = some raw := by
  cases raw with
  | mk n rows p0 p1 basis output =>
    simp [extractTwoPhaseDescriptor, rawDescriptorJson, jsonArr_get, jsonStr_get,
      jsonNat_getNat, jsonNatArray_extract]


/-- Conditional on ASCII and JSON text decoding to the constructed value,
    a validated descriptor has a body accepted by the modeled recognizer. -/
theorem serializedValidDescriptor_has_recognizedBody (bytes : List (Fin 256)) (text : String)
    (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (ha : decodeAscii bytes = some text)
    (hj : (Lean.Json.parse text).toOption = some (rawDescriptorJson raw))
    (hv : rawDescriptorToValidated raw = some ⟨n, d⟩)
    (state : SharedDyadicState n) :
    ∃ ops body, recognizeModeledSource (encodeNumericHeader bytes ++ body) = some ⟨n, (d, ops)⟩ := by
  exact encodedValidSource_has_recognizedBody bytes text (rawDescriptorJson raw) raw n d
    ha hj (rawDescriptorJson_extract raw) hv state

end SectorSimulation
