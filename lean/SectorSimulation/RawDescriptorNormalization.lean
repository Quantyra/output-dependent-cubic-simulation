import SectorSimulation.CanonicalMaskNormalization
namespace SectorSimulation

def normalizeRawDescriptor (raw : RawTwoPhaseDescriptor) : RawTwoPhaseDescriptor :=
  { raw with phase0 := sortedNormalizeMasks raw.phase0, phase1 := sortedNormalizeMasks raw.phase1 }

theorem sortedNormalizeMasks_subset (masks : List Nat) :
    ∀ k, k ∈ sortedNormalizeMasks masks → k ∈ masks := by
  intro k hk
  have odd := (sortedNormalizeMasks_odd_count k masks).mp hk
  apply List.count_pos_iff.mp
  omega

theorem sortedNormalizeMasks_all (masks : List Nat) (p : Nat → Bool)
    (h : masks.all p = true) : (sortedNormalizeMasks masks).all p = true := by
  apply List.all_eq_true.mpr
  intro k hk
  exact List.all_eq_true.mp h k (sortedNormalizeMasks_subset masks k hk)

theorem normalizedRaw_phases (raw : RawTwoPhaseDescriptor) (n : Nat) (x : BinaryVector n) :
    evalPhase ((normalizeRawDescriptor raw).phase0.map (rawMask (n := n))) x =
      evalPhase (raw.phase0.map rawMask) x ∧
    evalPhase ((normalizeRawDescriptor raw).phase1.map (rawMask (n := n))) x =
      evalPhase (raw.phase1.map rawMask) x := by
  exact ⟨sortedNormalizeMasks_eval raw.phase0 x, sortedNormalizeMasks_eval raw.phase1 x⟩

theorem normalizedRaw_boundary (raw : RawTwoPhaseDescriptor) :
    (normalizeRawDescriptor raw).n = raw.n ∧ (normalizeRawDescriptor raw).rows = raw.rows ∧
    (normalizeRawDescriptor raw).basis = raw.basis ∧ (normalizeRawDescriptor raw).output = raw.output := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem normalizeRawDescriptor_idempotent (raw : RawTwoPhaseDescriptor) :
    normalizeRawDescriptor (normalizeRawDescriptor raw) = normalizeRawDescriptor raw := by
  cases raw
  simp [normalizeRawDescriptor, sortedNormalizeMasks_idempotent]

theorem normalizedRaw_maskChecks (raw : RawTwoPhaseDescriptor)
    (h0 : raw.phase0.all (fun m => m < 2 ^ raw.n) = true)
    (h1 : raw.phase1.all (fun m => m < 2 ^ raw.n) = true) :
    (normalizeRawDescriptor raw).phase0.all (fun m => m < 2 ^ raw.n) = true ∧
    (normalizeRawDescriptor raw).phase1.all (fun m => m < 2 ^ raw.n) = true := by
  exact ⟨sortedNormalizeMasks_all raw.phase0 _ h0, sortedNormalizeMasks_all raw.phase1 _ h1⟩

theorem normalizedRaw_degreeChecks (raw : RawTwoPhaseDescriptor) (n : Nat) (bound : Nat)
    (h0 : phaseWithinDegree bound (raw.phase0.map (rawMask (n := n))) = true)
    (h1 : phaseWithinDegree bound (raw.phase1.map (rawMask (n := n))) = true) :
    phaseWithinDegree bound ((normalizeRawDescriptor raw).phase0.map (rawMask (n := n))) = true ∧
    phaseWithinDegree bound ((normalizeRawDescriptor raw).phase1.map (rawMask (n := n))) = true := by
  simp only [phaseWithinDegree, List.all_map] at h0 h1 ⊢
  exact ⟨sortedNormalizeMasks_all raw.phase0 _ h0, sortedNormalizeMasks_all raw.phase1 _ h1⟩

end SectorSimulation
