import SectorSimulation.NumericHeaderBytes
namespace SectorSimulation

theorem numeric_native_header_sound (gates : List NativeGate) (bytes : List (Fin 256))
    (body : List NativeGate) (h : decodeNumericHeader gates = some (bytes, body)) :
    gates = encodeNumericHeader bytes ++ body := by
  unfold decodeNumericHeader at h
  cases hd : decodeNativeByteHeader gates with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨fields, suffix⟩
    simp [hd] at h
    rcases h with ⟨rfl, rfl⟩
    have hg := native_byte_header_sound gates fields suffix hd
    have hf : (fun b : HeaderByte => headerByteFromNat (headerByteToFin b).val) = id := by
      funext b
      exact headerByte_numeric_roundtrip b
    simpa [encodeNumericHeader, List.map_map, Function.comp_def, hf] using hg

theorem numeric_native_header_iff (gates : List NativeGate) (bytes : List (Fin 256))
    (body : List NativeGate) :
    decodeNumericHeader gates = some (bytes, body) ↔ gates = encodeNumericHeader bytes ++ body := by
  constructor
  · exact numeric_native_header_sound gates bytes body
  · intro h; subst gates; exact numeric_native_header_roundtrip bytes body

end SectorSimulation
