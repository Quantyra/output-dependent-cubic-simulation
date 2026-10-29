import SectorSimulation.NativeGateHeader
namespace SectorSimulation

structure HeaderByte where
  b7 : Bool
  b6 : Bool
  b5 : Bool
  b4 : Bool
  b3 : Bool
  b2 : Bool
  b1 : Bool
  b0 : Bool
  deriving DecidableEq, Repr

def headerByteBits (b : HeaderByte) : List Bool :=
  [b.b7, b.b6, b.b5, b.b4, b.b3, b.b2, b.b1, b.b0]

def headerBytesBits (bytes : List HeaderByte) : List Bool := bytes.flatMap headerByteBits

def parseHeaderBytes : List Bool → Option (List HeaderByte)
  | [] => some []
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: rest =>
    (parseHeaderBytes rest).map fun bytes => ⟨b7,b6,b5,b4,b3,b2,b1,b0⟩ :: bytes
  | _ => none

theorem parse_header_bytes_roundtrip (bytes : List HeaderByte) :
    parseHeaderBytes (headerBytesBits bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    change parseHeaderBytes (List.flatMap headerByteBits rest) = some rest at ih
    cases b
    simp [headerBytesBits, headerByteBits, parseHeaderBytes, ih]

def encodeNativeByteHeader (bytes : List HeaderByte) : List NativeGate :=
  encodeNativeHeader (headerBytesBits bytes)

def decodeNativeByteHeader (gates : List NativeGate) : Option (List HeaderByte × List NativeGate) :=
  match decodeNativeHeader gates with
  | none => none
  | some (bits, body) => (parseHeaderBytes bits).map fun bytes => (bytes, body)

theorem native_byte_header_roundtrip (bytes : List HeaderByte) (body : List NativeGate) :
    decodeNativeByteHeader (encodeNativeByteHeader bytes ++ body) = some (bytes, body) := by
  simp [decodeNativeByteHeader, encodeNativeByteHeader, decode_encode_native_header, parse_header_bytes_roundtrip]

theorem native_byte_header_rejects_incomplete (gates : List NativeGate) (bits : List Bool) (body : List NativeGate)
    (h : decodeNativeHeader gates = some (bits, body)) (bad : parseHeaderBytes bits = none) :
    decodeNativeByteHeader gates = none := by
  simp [decodeNativeByteHeader, h, bad]

end SectorSimulation
