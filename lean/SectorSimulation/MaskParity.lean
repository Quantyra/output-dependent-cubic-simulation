import SectorSimulation.ToggleMaskNormalization
namespace SectorSimulation

def maskParity (key : Nat) (masks : List Nat) : Bool :=
  masks.foldr (fun m b => Bool.xor (decide (key = m)) b) false

theorem toggleMask_membership (key m : Nat) (acc : List Nat) (h : acc.Nodup) :
    decide (key ∈ toggleMask m acc) = Bool.xor (decide (key = m)) (decide (key ∈ acc)) := by
  by_cases hm : m ∈ acc <;> by_cases he : key = m
  · subst key; simp [toggleMask, hm, h.not_mem_erase]
  · simp [toggleMask, hm, h.mem_erase_iff, he]
  · subst key; simp [toggleMask, hm]
  · simp [toggleMask, hm, he]

theorem normalizeMasks_fold_membership (key : Nat) (masks acc : List Nat) (h : acc.Nodup) :
    decide (key ∈ masks.foldl (fun acc m => toggleMask m acc) acc) =
      Bool.xor (decide (key ∈ acc)) (maskParity key masks) := by
  induction masks generalizing acc with
  | nil => simp [maskParity]
  | cons m rest ih =>
    calc
      decide (key ∈ (m :: rest).foldl (fun acc m => toggleMask m acc) acc) =
          Bool.xor (decide (key ∈ toggleMask m acc)) (maskParity key rest) :=
        ih (toggleMask m acc) (toggleMask_nodup m acc h)
      _ = Bool.xor (decide (key ∈ acc)) (maskParity key (m :: rest)) := by
        have ht := toggleMask_membership key m acc h
        have hc := congrArg (fun b => Bool.xor b (maskParity key rest)) ht
        apply hc.trans
        simp only [maskParity, List.foldr_cons]
        cases decide (key = m) <;> cases decide (key ∈ acc) <;>
          cases rest.foldr (fun m b => Bool.xor (decide (key = m)) b) false <;> rfl

theorem sortedNormalizeMasks_membership (key : Nat) (masks : List Nat) :
    decide (key ∈ sortedNormalizeMasks masks) = maskParity key masks := by
  have hp := (List.mergeSort_perm (normalizeMasks masks) (fun a b => a ≤ b)).mem_iff (a := key)
  have hm : decide (key ∈ sortedNormalizeMasks masks) = decide (key ∈ normalizeMasks masks) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, sortedNormalizeMasks] using hp
  rw [hm]
  simpa [normalizeMasks] using normalizeMasks_fold_membership key masks [] (by simp)

end SectorSimulation
