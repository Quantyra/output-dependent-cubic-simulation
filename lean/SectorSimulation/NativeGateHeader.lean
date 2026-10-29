import SectorSimulation.NativeHeaderSound
namespace SectorSimulation

structure NativeGate where
  tag : String
  wires : List Nat
  deriving DecidableEq, Repr

def nativeX0 : NativeGate := ⟨"X", [0]⟩
def nativeZ0 : NativeGate := ⟨"Z", [0]⟩
def nativeH0 : NativeGate := ⟨"H", [0]⟩

def encodeNativeHeader : List Bool → List NativeGate
  | [] => [nativeH0, nativeH0]
  | false :: rest => nativeX0 :: nativeX0 :: encodeNativeHeader rest
  | true :: rest => nativeZ0 :: nativeZ0 :: encodeNativeHeader rest

def decodeNativeHeader : List NativeGate → Option (List Bool × List NativeGate)
  | a :: b :: rest =>
      if a = nativeH0 ∧ b = nativeH0 then some ([], rest)
      else if a = nativeX0 ∧ b = nativeX0 then
        (decodeNativeHeader rest).map fun (bits, body) => (false :: bits, body)
      else if a = nativeZ0 ∧ b = nativeZ0 then
        (decodeNativeHeader rest).map fun (bits, body) => (true :: bits, body)
      else none
  | _ => none

theorem decode_encode_native_header (bits : List Bool) (body : List NativeGate) :
    decodeNativeHeader (encodeNativeHeader bits ++ body) = some (bits, body) := by
  induction bits with
  | nil => simp [encodeNativeHeader, decodeNativeHeader]
  | cons bit rest ih =>
    cases bit <;> simp [encodeNativeHeader, decodeNativeHeader, nativeX0, nativeZ0, nativeH0, ih]

theorem native_header_length (bits : List Bool) : (encodeNativeHeader bits).length = 2 * bits.length + 2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [encodeNativeHeader, ih, Nat.mul_succ, Nat.add_assoc]

theorem decode_native_header_sound (gates : List NativeGate) (bits : List Bool) (body : List NativeGate)
    (h : decodeNativeHeader gates = some (bits, body)) : gates = encodeNativeHeader bits ++ body := by
  fun_induction decodeNativeHeader gates generalizing bits body with
  | case1 a b rest hp =>
    rcases hp with ⟨rfl, rfl⟩
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case2 a b rest hn hp ih =>
    rcases hp with ⟨rfl, rfl⟩
    cases hd : decodeNativeHeader rest with
    | none => simp [hd] at h
    | some pair =>
      rcases pair with ⟨bs, suffix⟩
      simp [hd] at h
      rcases h with ⟨rfl, rfl⟩
      simp [encodeNativeHeader, ih bs suffix hd]
  | case3 a b rest hn hx hp ih =>
    rcases hp with ⟨rfl, rfl⟩
    cases hd : decodeNativeHeader rest with
    | none => simp [hd] at h
    | some pair =>
      rcases pair with ⟨bs, suffix⟩
      simp [hd] at h
      rcases h with ⟨rfl, rfl⟩
      simp [encodeNativeHeader, ih bs suffix hd]
  | case4 => simp at h
  | case5 => simp at h

end SectorSimulation
