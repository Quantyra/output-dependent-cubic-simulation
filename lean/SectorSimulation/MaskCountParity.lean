import SectorSimulation.MaskParity
import Init.Data.List.Count
namespace SectorSimulation

theorem maskParity_count (key : Nat) (masks : List Nat) :
    maskParity key masks = decide (masks.count key % 2 = 1) := by
  induction masks with
  | nil => rfl
  | cons m rest ih =>
    by_cases he : key = m
    · subst m
      simp only [maskParity, List.foldr_cons, decide_true, List.count_cons_self]
      change Bool.xor true (maskParity key rest) = decide ((rest.count key + 1) % 2 = 1)
      rw [ih]
      by_cases h : rest.count key % 2 = 1
      · have h2 : (rest.count key + 1) % 2 ≠ 1 := by omega
        simp [h, h2]
      · have h2 : (rest.count key + 1) % 2 = 1 := by omega
        simp [h, h2]
    · have hn : m ≠ key := Ne.symm he
      simp only [maskParity, List.foldr_cons, he, decide_false, Bool.false_xor, List.count_cons_of_ne hn]
      exact ih

theorem sortedNormalizeMasks_odd_count (key : Nat) (masks : List Nat) :
    key ∈ sortedNormalizeMasks masks ↔ masks.count key % 2 = 1 := by
  have h := sortedNormalizeMasks_membership key masks
  rw [maskParity_count] at h
  simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp h

end SectorSimulation
