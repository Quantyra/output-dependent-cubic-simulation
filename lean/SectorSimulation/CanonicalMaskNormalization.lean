import SectorSimulation.MaskCountParity
namespace SectorSimulation

/-- A sorted duplicate-free list with the odd-count membership property is canonical. -/
theorem sortedNormalizeMasks_unique (masks candidate : List Nat)
    (hn : candidate.Nodup) (hs : candidate.Pairwise (fun a b => a ≤ b))
    (hm : ∀ k, k ∈ candidate ↔ masks.count k % 2 = 1) :
    sortedNormalizeMasks masks = candidate := by
  have hp : (sortedNormalizeMasks masks).Perm candidate := by
    apply List.perm_iff_count.mpr
    intro key
    rw [(sortedNormalizeMasks_nodup masks).count, hn.count]
    by_cases h : key ∈ candidate
    · have hc : masks.count key % 2 = 1 := (hm key).mp h
      have ho : key ∈ sortedNormalizeMasks masks := (sortedNormalizeMasks_odd_count key masks).mpr hc
      simp [h, ho]
    · have hc : masks.count key % 2 ≠ 1 := fun hh => h ((hm key).mpr hh)
      have ho : key ∉ sortedNormalizeMasks masks := fun hh => hc ((sortedNormalizeMasks_odd_count key masks).mp hh)
      simp [h, ho]
  exact hp.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    (sortedNormalizeMasks_sorted masks) hs

theorem sortedNormalizeMasks_perm (a b : List Nat) (h : a.Perm b) :
    sortedNormalizeMasks a = sortedNormalizeMasks b := by
  apply sortedNormalizeMasks_unique a (sortedNormalizeMasks b)
    (sortedNormalizeMasks_nodup b) (sortedNormalizeMasks_sorted b)
  intro k
  rw [sortedNormalizeMasks_odd_count, h.count_eq]

theorem sortedNormalizeMasks_idempotent (masks : List Nat) :
    sortedNormalizeMasks (sortedNormalizeMasks masks) = sortedNormalizeMasks masks := by
  apply sortedNormalizeMasks_unique (sortedNormalizeMasks masks) (sortedNormalizeMasks masks)
    (sortedNormalizeMasks_nodup masks) (sortedNormalizeMasks_sorted masks)
  intro k
  rw [(sortedNormalizeMasks_nodup masks).count]
  by_cases h : k ∈ sortedNormalizeMasks masks <;> simp [h]

end SectorSimulation
