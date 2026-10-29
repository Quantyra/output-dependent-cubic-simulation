import SectorSimulation.ClearProgramInvariant
namespace SectorSimulation

theorem clearRows_target {n : Nat} (rows : List (Fin n)) (J : BinaryMatrix n)
    (y : BinaryVector n) (pivot target : Fin n)
    (hn : rows.Nodup) (hp : pivot ∉ rows) (ht : target ∈ rows)
    (hone : J pivot pivot = true) (hval : J target pivot = true) :
    (applyRowProgram (rows.map fun row => RowOperation.add row pivot) J y).1 target pivot = false := by
  induction rows generalizing J y with
  | nil => simp at ht
  | cons row rest ih =>
    have hd := List.nodup_cons.mp hn
    have hpr : pivot ∉ rest := by intro h; exact hp (by simp [h])
    have hrowp : row ≠ pivot := by intro h; subst row; exact hp (by simp)
    simp only [List.map_cons, applyRowProgram, List.foldl_cons, applyRowOperation, if_neg hrowp]
    by_cases heq : row = target
    · subst row
      have hrest : ∀ op ∈ rest.map (fun r => RowOperation.add r pivot),
          ∃ r, r ≠ target ∧ op = RowOperation.add r pivot := by
        intro op hop
        obtain ⟨r, hr, he⟩ := List.mem_map.mp hop
        have hne : r ≠ target := by intro h; subst r; exact hd.1 hr
        exact ⟨r, hne, he.symm⟩
      have hh := addProgram_preserves_row (rest.map fun r => RowOperation.add r pivot)
        (rowAdd J target pivot) (vectorAddRow y target pivot) pivot target pivot hrest
      have hv := add_clears_column J pivot target hval hone
      simpa [applyRowProgram, applyRowOperation, hv] using hh.trans hv
    · have htarget : target ∈ rest := by simpa [heq, Ne.symm heq] using ht
      have hnewpivot : rowAdd J row pivot pivot pivot = true := by
        simpa [rowAdd, Ne.symm hrowp] using hone
      have hnewtarget : rowAdd J row pivot target pivot = true := by
        simpa [rowAdd, Ne.symm heq] using hval
      have hh := ih (rowAdd J row pivot) (vectorAddRow y row pivot) hd.2 hpr htarget hnewpivot hnewtarget
      simpa [applyRowProgram, applyRowOperation] using hh

theorem clearProgram_clears_column {n : Nat} (J : BinaryMatrix n) (y : BinaryVector n)
    (pivot target : Fin n) (hne : target ≠ pivot) (hone : J pivot pivot = true) :
    (applyRowProgram (clearColumnOps J pivot) J y).1 target pivot = false := by
  let rows := (List.finRange n).filter fun row => decide (row ≠ pivot) && J row pivot
  have hn : rows.Nodup := List.Nodup.sublist List.filter_sublist (List.nodup_finRange n)
  have hp : pivot ∉ rows := by simp [rows]
  have heq : clearColumnOps J pivot = rows.map (fun row => RowOperation.add row pivot) := rfl
  cases hv : J target pivot with
  | true =>
    have ht : target ∈ rows := by simp [rows, hne, hv]
    rw [heq]
    exact clearRows_target rows J y pivot target hn hp ht hone hv
  | false =>
    have hops : ∀ op ∈ clearColumnOps J pivot, ∃ row, row ≠ target ∧ op = RowOperation.add row pivot := by
      intro op hm
      obtain ⟨row, _, hr, he⟩ := clearColumnOps_eligible J pivot op hm
      have hrne : row ≠ target := by intro h; subst row; simp [hv] at hr
      exact ⟨row, hrne, he⟩
    have hh := addProgram_preserves_row (clearColumnOps J pivot) J y pivot target pivot hops
    simpa [hv] using hh

end SectorSimulation
