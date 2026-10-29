import SectorSimulation.NativeHeaderBytes
namespace SectorSimulation

theorem parse_header_bytes_sound (bits : List Bool) (bytes : List HeaderByte)
    (h : parseHeaderBytes bits = some bytes) : headerBytesBits bytes = bits := by
  fun_induction parseHeaderBytes bits generalizing bytes with
  | case1 => simp at h; subst bytes; rfl
  | case2 b7 b6 b5 b4 b3 b2 b1 b0 rest ih =>
    cases hp : parseHeaderBytes rest with
    | none => simp [hp] at h
    | some tail =>
      simp [hp] at h
      subst bytes
      have hh := ih tail hp
      change List.flatMap headerByteBits tail = rest at hh
      simp [headerBytesBits, headerByteBits, hh]
  | case3 => simp at h

theorem native_byte_header_sound (gates : List NativeGate) (bytes : List HeaderByte)
    (body : List NativeGate) (h : decodeNativeByteHeader gates = some (bytes, body)) :
    gates = encodeNativeByteHeader bytes ++ body := by
  unfold decodeNativeByteHeader at h
  cases hd : decodeNativeHeader gates with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨bits, suffix⟩
    cases hp : parseHeaderBytes bits with
    | none => simp [hd, hp] at h
    | some parsed =>
      simp [hd, hp] at h
      rcases h with ⟨rfl, rfl⟩
      have hb := parse_header_bytes_sound bits parsed hp
      have hg := decode_native_header_sound gates bits suffix hd
      simpa [encodeNativeByteHeader, hb] using hg

theorem parsed_header_bits_length (bits : List Bool) (bytes : List HeaderByte)
    (h : parseHeaderBytes bits = some bytes) : bits.length = 8 * bytes.length := by
  have hlen : ∀ bs : List HeaderByte, (headerBytesBits bs).length = 8 * bs.length := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b rest ih =>
      change (List.flatMap headerByteBits rest).length = 8 * rest.length at ih
      simp only [headerBytesBits, List.flatMap_cons, List.length_append, headerByteBits, List.length_cons, List.length_nil, Nat.mul_succ]
      omega
  rw [← parse_header_bytes_sound bits bytes h]
  exact hlen bytes

end SectorSimulation
