import SectorSimulation.PivotStepInvariants
namespace SectorSimulation

theorem addProgram_preserves_row {n : Nat} (ops : List (RowOperation n))
    (J : BinaryMatrix n) (y : BinaryVector n) (pivot fixedRow col : Fin n)
    (hops : ∀ op ∈ ops, ∃ row, row ≠ fixedRow ∧ op = RowOperation.add row pivot) :
    (applyRowProgram ops J y).1 fixedRow col = J fixedRow col := by
  induction ops generalizing J y with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨row, hneq, hop⟩ := hops op (by simp)
    subst op
    have hrest : ∀ op ∈ rest, ∃ row, row ≠ fixedRow ∧ op = RowOperation.add row pivot := by
      intro op hm; exact hops op (by simp [hm])
    simp only [applyRowProgram, List.foldl_cons]
    by_cases hp : row = pivot
    · simp [applyRowOperation, hp]
      exact ih J y hrest
    · simp only [applyRowOperation, if_neg hp]
      have hh := ih (rowAdd J row pivot) (vectorAddRow y row pivot) hrest
      simpa [applyRowProgram, rowAdd, Ne.symm hneq, applyRowOperation] using hh

theorem clearProgram_preserves_pivot {n : Nat} (J : BinaryMatrix n) (y : BinaryVector n)
    (pivot col : Fin n) :
    (applyRowProgram (clearColumnOps J pivot) J y).1 pivot col = J pivot col := by
  apply addProgram_preserves_row _ J y pivot pivot col
  intro op hop
  obtain ⟨row, hne, _, heq⟩ := clearColumnOps_eligible J pivot op hop
  exact ⟨row, hne, heq⟩

end SectorSimulation
