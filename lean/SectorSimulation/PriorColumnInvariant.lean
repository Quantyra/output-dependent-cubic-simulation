import SectorSimulation.ClearColumnComplete
namespace SectorSimulation

theorem rowAdd_preserves_zero_source_column {n : Nat} (J : BinaryMatrix n)
    (dest src old : Fin n) (hzero : J src old = false) :
    ∀ row, rowAdd J dest src row old = J row old := by
  intro row
  by_cases h : row = dest
  · subst row; simp [rowAdd, hzero]
  · simp [rowAdd, h]

theorem addProgram_preserves_zero_source_column {n : Nat} (ops : List (RowOperation n))
    (J : BinaryMatrix n) (y : BinaryVector n) (pivot old : Fin n)
    (hzero : J pivot old = false)
    (hops : ∀ op ∈ ops, ∃ row, op = RowOperation.add row pivot) :
    ∀ row, (applyRowProgram ops J y).1 row old = J row old := by
  induction ops generalizing J y with
  | nil => intro row; rfl
  | cons op rest ih =>
    obtain ⟨dest, hop⟩ := hops op (by simp)
    subst op
    have hrest : ∀ op ∈ rest, ∃ row, op = RowOperation.add row pivot := by
      intro op hm; exact hops op (by simp [hm])
    simp only [applyRowProgram, List.foldl_cons]
    by_cases heq : dest = pivot
    · simp [applyRowOperation, heq]
      exact ih J y hzero hrest
    · simp only [applyRowOperation, if_neg heq]
      have hcol := rowAdd_preserves_zero_source_column J dest pivot old hzero
      have hnew : rowAdd J dest pivot pivot old = false := by rw [hcol pivot, hzero]
      have hh := ih (rowAdd J dest pivot) (vectorAddRow y dest pivot) hnew hrest
      intro row
      have hf := hh row
      simpa [applyRowProgram, applyRowOperation, hcol row] using hf

theorem clearProgram_preserves_zero_source_column {n : Nat} (J : BinaryMatrix n)
    (y : BinaryVector n) (pivot old : Fin n) (hzero : J pivot old = false) :
    ∀ row, (applyRowProgram (clearColumnOps J pivot) J y).1 row old = J row old := by
  apply addProgram_preserves_zero_source_column _ J y pivot old hzero
  intro op hm
  obtain ⟨row, _, _, he⟩ := clearColumnOps_eligible J pivot op hm
  exact ⟨row, he⟩

theorem swap_preserves_unit_column {n : Nat} (J : BinaryMatrix n) (old a b : Fin n)
    (ha : a ≠ old) (hb : b ≠ old)
    (hunit : ∀ i, J i old = decide (i = old)) :
    ∀ i, rowSwap J a b i old = J i old := by
  intro i
  by_cases hia : i = a
  · subst i; simp [rowSwap, hunit, ha, hb]
  · by_cases hib : i = b
    · subst i; simp [rowSwap, hia, hunit, ha, hb]
    · simp [rowSwap, hia, hib]

theorem pivotStep_preserves_prior_unit {n : Nat} (J : BinaryMatrix n)
    (y : BinaryVector n) (old pivot row : Fin n)
    (hold : old.val < pivot.val) (hfind : findPivot J pivot = some row)
    (hunit : ∀ i, J i old = decide (i = old)) :
    ∀ i, (applyRowProgram (RowOperation.swap pivot row ::
      clearColumnOps (rowSwap J pivot row) pivot) J y).1 i old = J i old := by
  have hp : pivot ≠ old := by intro he; have := congrArg Fin.val he; omega
  have hr : row ≠ old := by
    have hf := (findPivot_sound J pivot row hfind).1
    intro he; have := congrArg Fin.val he; omega
  have hswap := swap_preserves_unit_column J old pivot row hp hr hunit
  have hzero : rowSwap J pivot row pivot old = false := by
    rw [hswap pivot, hunit pivot]
    simp [hp]
  intro i
  have hc := clearProgram_preserves_zero_source_column (rowSwap J pivot row)
    (vectorSwap y pivot row) pivot old hzero i
  simpa [applyRowProgram, applyRowOperation, hswap i] using hc

end SectorSimulation
