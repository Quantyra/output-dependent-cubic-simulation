import SectorSimulation.PhaseNormalization
import Init.Data.List.Sort.Lemmas
import SectorSimulation.NativeJsonDescriptor
namespace SectorSimulation

def toggleMask (m : Nat) (acc : List Nat) : List Nat :=
  if m ∈ acc then acc.erase m else m :: acc

def normalizeMasks (masks : List Nat) : List Nat :=
  masks.foldl (fun acc m => toggleMask m acc) []

theorem toggleMask_eval {n : Nat} (m : Nat) (acc : List Nat) (x : BinaryVector n) :
    evalPhase ((toggleMask m acc).map rawMask) x =
      Bool.xor (evalMonomial (rawMask m) x) (evalPhase (acc.map rawMask) x) := by
  by_cases h : m ∈ acc
  · have hp : evalPhase (acc.map rawMask) x =
        evalPhase ((m :: acc.erase m).map rawMask) x :=
      evalPhase_perm ((List.perm_cons_erase h).map rawMask) x
    simp only [List.map_cons, evalPhase_cons] at hp
    simp only [toggleMask, if_pos h]
    rw [hp]
    cases evalMonomial (rawMask m) x <;> cases evalPhase ((acc.erase m).map rawMask) x <;> rfl
  · simp [toggleMask, h, evalPhase_cons]

theorem normalizeMasks_fold_eval {n : Nat} (masks acc : List Nat) (x : BinaryVector n) :
    evalPhase ((masks.foldl (fun acc m => toggleMask m acc) acc).map rawMask) x =
      Bool.xor (evalPhase (acc.map rawMask) x) (evalPhase (masks.map rawMask) x) := by
  induction masks generalizing acc with
  | nil => simp [evalPhase_empty]
  | cons m rest ih =>
    simp only [List.foldl_cons, ih, toggleMask_eval, List.map_cons, evalPhase_cons]
    cases evalPhase (acc.map rawMask) x <;> cases evalPhase (rest.map rawMask) x <;>
      cases evalMonomial (rawMask m) x <;> rfl

theorem normalizeMasks_eval {n : Nat} (masks : List Nat) (x : BinaryVector n) :
    evalPhase ((normalizeMasks masks).map rawMask) x = evalPhase (masks.map rawMask) x := by
  simpa [normalizeMasks, evalPhase_empty] using normalizeMasks_fold_eval masks [] x


theorem toggleMask_nodup (m : Nat) (acc : List Nat) (h : acc.Nodup) :
    (toggleMask m acc).Nodup := by
  by_cases hm : m ∈ acc
  · simpa [toggleMask, hm] using h.erase m
  · simp [toggleMask, hm, h]

theorem normalizeMasks_fold_nodup (masks acc : List Nat) (h : acc.Nodup) :
    (masks.foldl (fun acc m => toggleMask m acc) acc).Nodup := by
  induction masks generalizing acc with
  | nil => exact h
  | cons m rest ih =>
    simp only [List.foldl_cons]
    exact ih (toggleMask m acc) (toggleMask_nodup m acc h)

theorem normalizeMasks_nodup (masks : List Nat) : (normalizeMasks masks).Nodup := by
  exact normalizeMasks_fold_nodup masks [] (by simp)

def sortedNormalizeMasks (masks : List Nat) : List Nat :=
  (normalizeMasks masks).mergeSort (fun a b => a ≤ b)

theorem sortedNormalizeMasks_eval {n : Nat} (masks : List Nat) (x : BinaryVector n) :
    evalPhase ((sortedNormalizeMasks masks).map rawMask) x = evalPhase (masks.map rawMask) x := by
  have hp := (List.mergeSort_perm (normalizeMasks masks) (fun a b => a ≤ b)).map (rawMask (n := n))
  exact (evalPhase_perm hp x).trans (normalizeMasks_eval masks x)

theorem sortedNormalizeMasks_nodup (masks : List Nat) : (sortedNormalizeMasks masks).Nodup := by
  exact (List.mergeSort_perm (normalizeMasks masks) (fun a b => a ≤ b)).nodup_iff.mpr (normalizeMasks_nodup masks)


theorem sortedNormalizeMasks_sorted (masks : List Nat) :
    (sortedNormalizeMasks masks).Pairwise (fun a b => a ≤ b) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c hab hbc; exact decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total a b)
    (normalizeMasks masks)
  simpa [sortedNormalizeMasks] using h

end SectorSimulation
