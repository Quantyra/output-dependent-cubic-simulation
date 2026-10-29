import SectorSimulation.GaussianSolveChecked
namespace SectorSimulation

theorem swap_pivot_entry {n : Nat} (J : BinaryMatrix n) (column row : Fin n)
    (h : J row column = true) : rowSwap J column row column column = true := by
  simp [rowSwap, h]

theorem add_clears_column {n : Nat} (J : BinaryMatrix n) (column row : Fin n)
    (hrow : J row column = true) (hpivot : J column column = true) :
    rowAdd J row column row column = false := by
  simp [rowAdd, hrow, hpivot]

theorem add_other_row_unchanged {n : Nat} (J : BinaryMatrix n) (dest src other col : Fin n)
    (h : other ≠ dest) : rowAdd J dest src other col = J other col := by
  simp [rowAdd, h]

theorem add_preserves_pivot_row {n : Nat} (J : BinaryMatrix n) (dest pivot col : Fin n)
    (h : dest ≠ pivot) : rowAdd J dest pivot pivot col = J pivot col := by
  exact add_other_row_unchanged J dest pivot pivot col (Ne.symm h)

theorem clearColumnOps_contains {n : Nat} (J : BinaryMatrix n) (column row : Fin n)
    (hneq : row ≠ column) (hone : J row column = true) :
    RowOperation.add row column ∈ clearColumnOps J column := by
  apply List.mem_map.mpr
  refine ⟨row, ?_, rfl⟩
  simp [List.mem_filter, hneq, hone]

theorem clearColumnOps_eligible {n : Nat} (J : BinaryMatrix n) (column : Fin n)
    (op : RowOperation n) (h : op ∈ clearColumnOps J column) :
    ∃ row, row ≠ column ∧ J row column = true ∧ op = RowOperation.add row column := by
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp h
  have parts : row ≠ column ∧ J row column = true := by
    simpa [List.mem_filter] using hrow
  exact ⟨row, parts.1, parts.2, heq.symm⟩

end SectorSimulation
