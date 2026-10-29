import SectorSimulation.NativeHeaderBits
namespace SectorSimulation

theorem decode_header_bits_sound (gates : List HeaderGate) (bits : List Bool) (body : List HeaderGate)
    (h : decodeHeaderBits gates = some (bits, body)) : gates = encodeHeaderBits bits ++ body := by
  fun_induction decodeHeaderBits gates generalizing bits body with
  | case1 rest =>
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case2 rest ih =>
    cases hd : decodeHeaderBits rest with
    | none => simp [hd] at h
    | some p =>
      rcases p with ⟨bs, suffix⟩
      simp [hd] at h
      rcases h with ⟨rfl, rfl⟩
      simp [encodeHeaderBits, ih bs suffix hd]
  | case3 rest ih =>
    cases hd : decodeHeaderBits rest with
    | none => simp [hd] at h
    | some p =>
      rcases p with ⟨bs, suffix⟩
      simp [hd] at h
      rcases h with ⟨rfl, rfl⟩
      simp [encodeHeaderBits, ih bs suffix hd]
  | case4 => simp at h

end SectorSimulation
