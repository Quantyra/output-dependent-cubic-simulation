import SectorSimulation.NativeHeaderBytesSound
namespace SectorSimulation

def headerByteValue (b : HeaderByte) : Nat :=
  (if b.b7 then 128 else 0) + (if b.b6 then 64 else 0) +
  (if b.b5 then 32 else 0) + (if b.b4 then 16 else 0) +
  (if b.b3 then 8 else 0) + (if b.b2 then 4 else 0) +
  (if b.b1 then 2 else 0) + (if b.b0 then 1 else 0)

def headerByteFromNat (v : Nat) : HeaderByte :=
  ⟨v.testBit 7, v.testBit 6, v.testBit 5, v.testBit 4,
    v.testBit 3, v.testBit 2, v.testBit 1, v.testBit 0⟩

theorem headerByteValue_lt_256 (b : HeaderByte) : headerByteValue b < 256 := by
  cases b with
  | mk b7 b6 b5 b4 b3 b2 b1 b0 =>
    cases b7 <;> cases b6 <;> cases b5 <;> cases b4 <;>
      cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> decide

theorem headerByte_numeric_roundtrip (b : HeaderByte) : headerByteFromNat (headerByteValue b) = b := by
  cases b with
  | mk b7 b6 b5 b4 b3 b2 b1 b0 =>
    cases b7 <;> cases b6 <;> cases b5 <;> cases b4 <;>
      cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem numeric_headerByte_roundtrip (v : Fin 256) : headerByteValue (headerByteFromNat v.val) = v.val := by
  have hall : ∀ v : Fin 256, headerByteValue (headerByteFromNat v.val) = v.val := by decide
  exact hall v

def headerByteToFin (b : HeaderByte) : Fin 256 := ⟨headerByteValue b, headerByteValue_lt_256 b⟩

def encodeNumericHeader (bytes : List (Fin 256)) : List NativeGate :=
  encodeNativeByteHeader (bytes.map fun b => headerByteFromNat b.val)

def decodeNumericHeader (gates : List NativeGate) : Option (List (Fin 256) × List NativeGate) :=
  (decodeNativeByteHeader gates).map fun (bytes, body) => (bytes.map headerByteToFin, body)

theorem numeric_native_header_roundtrip (bytes : List (Fin 256)) (body : List NativeGate) :
    decodeNumericHeader (encodeNumericHeader bytes ++ body) = some (bytes, body) := by
  have hf : (fun b : Fin 256 => headerByteToFin (headerByteFromNat b.val)) = id := by
    funext b
    apply Fin.ext
    exact numeric_headerByte_roundtrip b
  simp [decodeNumericHeader, encodeNumericHeader, native_byte_header_roundtrip, List.map_map, Function.comp_def, hf]

end SectorSimulation
