import SectorSimulation.SourceValidation
namespace SectorSimulation

inductive HeaderGate where
  | x0 | z0 | h0 | other
  deriving DecidableEq, Repr

def encodeHeaderBits : List Bool → List HeaderGate
  | [] => [.h0, .h0]
  | false :: rest => .x0 :: .x0 :: encodeHeaderBits rest
  | true :: rest => .z0 :: .z0 :: encodeHeaderBits rest

def decodeHeaderBits : List HeaderGate → Option (List Bool × List HeaderGate)
  | .h0 :: .h0 :: rest => some ([], rest)
  | .x0 :: .x0 :: rest => (decodeHeaderBits rest).map fun (bits, body) => (false :: bits, body)
  | .z0 :: .z0 :: rest => (decodeHeaderBits rest).map fun (bits, body) => (true :: bits, body)
  | _ => none

theorem decode_encode_header_bits (bits : List Bool) (body : List HeaderGate) :
    decodeHeaderBits (encodeHeaderBits bits ++ body) = some (bits, body) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [encodeHeaderBits, decodeHeaderBits, ih]

theorem encoded_header_length (bits : List Bool) : (encodeHeaderBits bits).length = 2 * bits.length + 2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [encodeHeaderBits, ih, Nat.mul_succ, Nat.add_assoc]

end SectorSimulation
