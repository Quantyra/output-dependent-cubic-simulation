import SectorSimulation.RawDescriptorNormalization
namespace SectorSimulation

def normalizeAfterRawValidation (raw : RawTwoPhaseDescriptor) : Option RawTwoPhaseDescriptor := do
  let _ ← rawDescriptorToValidated raw
  pure (normalizeRawDescriptor raw)

theorem normalizeAfterRawValidation_rejects (raw : RawTwoPhaseDescriptor)
    (h : rawDescriptorToValidated raw = none) : normalizeAfterRawValidation raw = none := by
  simp [normalizeAfterRawValidation, h]

theorem normalizeAfterRawValidation_accepts (raw : RawTwoPhaseDescriptor) (n : Nat)
    (d : CircuitDescriptor n) (h : rawDescriptorToValidated raw = some ⟨n, d⟩) :
    normalizeAfterRawValidation raw = some (normalizeRawDescriptor raw) := by
  simp [normalizeAfterRawValidation, h]

theorem normalizedRaw_validation_preserved (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (h : rawDescriptorToValidated raw = some ⟨n,d⟩) :
    (rawDescriptorToValidated (normalizeRawDescriptor raw)).isSome = true := by
  unfold rawDescriptorToValidated at h
  repeat' split at h <;> simp_all
  rcases h with ⟨hlen, hrows, hp0, hp1, hb, hout, hv, hn, heq⟩
  simp only [sourceDescriptorValid, phasesAreCubic, Bool.and_eq_true, phaseWithinDegree, List.all_map] at hv
  have p0 := sortedNormalizeMasks_all raw.phase0 _ hv.1.1.1
  have p1 := sortedNormalizeMasks_all raw.phase1 _ hv.1.1.2
  have b0 : (sortedNormalizeMasks raw.phase0).all (fun m => m < 2 ^ raw.n) = true :=
    sortedNormalizeMasks_all raw.phase0 _ (List.all_eq_true.mpr (by intro k hk; exact decide_eq_true (hp0 k hk)))
  have b1 : (sortedNormalizeMasks raw.phase1).all (fun m => m < 2 ^ raw.n) = true :=
    sortedNormalizeMasks_all raw.phase1 _ (List.all_eq_true.mpr (by intro k hk; exact decide_eq_true (hp1 k hk)))
  have br : raw.rows.all (fun m => m < 2 ^ raw.n) = true :=
    List.all_eq_true.mpr (by intro k hk; exact decide_eq_true (hrows k hk))
  unfold rawDescriptorToValidated
  dsimp only [normalizeRawDescriptor]
  repeat' split <;> simp_all [sourceDescriptorValid, phasesAreCubic, phaseWithinDegree, List.all_map]
  all_goals
    rename_i hbad
    obtain ⟨x, hx, hge⟩ := hbad
    first
    | have hlt := hrows x hx; omega
    | have hlt := b0 x hx; omega
    | have hlt := b1 x hx; omega

end SectorSimulation
