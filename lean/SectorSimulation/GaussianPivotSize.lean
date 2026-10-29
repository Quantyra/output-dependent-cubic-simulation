import SectorSimulation.GaussianPivot
namespace SectorSimulation

theorem clearColumnOps_length {n : Nat} (J : BinaryMatrix n) (column : Fin n) :
    (clearColumnOps J column).length ≤ n := by
  unfold clearColumnOps
  rw [List.length_map]
  simpa using (List.length_filter_le (l := List.finRange n) (p := fun row => decide (row ≠ column) && J row column))

theorem pivotPrograms_length {n : Nat} (columns : List (Fin n)) (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (h : pivotPrograms columns J = some ops) :
    ops.length ≤ columns.length * (n + 1) := by
  induction columns generalizing J ops with
  | nil => simp [pivotPrograms] at h; subst ops; simp
  | cons column rest ih =>
    simp only [pivotPrograms] at h
    cases hp : findPivot J column with
    | none => simp [hp] at h
    | some row =>
      simp only [hp] at h
      cases ht : pivotPrograms rest (applyRowProgram (RowOperation.swap column row :: clearColumnOps (rowSwap J column row) column) J zeroVector).1 with
      | none => simp [ht] at h
      | some tail =>
        simp [ht] at h
        subst ops
        have htbound := ih _ tail ht
        have hb := clearColumnOps_length (rowSwap J column row) column
        simp only [List.length_append, List.length_cons, Nat.succ_mul]
        omega

theorem gaussianRowProgram_length {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (h : gaussianRowProgram J = some ops) :
    ops.length ≤ n * (n + 1) := by
  simpa using pivotPrograms_length (List.finRange n) J ops h

end SectorSimulation
