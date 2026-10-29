import SectorSimulation.PriorColumnInvariant
namespace SectorSimulation

theorem rowProgram_matrix_independent {n : Nat} (ops : List (RowOperation n))
    (J : BinaryMatrix n) (y z : BinaryVector n) :
    (applyRowProgram ops J y).1 = (applyRowProgram ops J z).1 := by
  induction ops generalizing J y z with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | swap a b =>
      simpa [applyRowProgram, applyRowOperation] using ih (rowSwap J a b) (vectorSwap y a b) (vectorSwap z a b)
    | add a b =>
      by_cases h : a = b
      · simpa [applyRowProgram, applyRowOperation, h] using ih J y z
      · simpa [applyRowProgram, applyRowOperation, h] using ih (rowAdd J a b) (vectorAddRow y a b) (vectorAddRow z a b)

theorem rowProgram_append {n : Nat} (ops tail : List (RowOperation n))
    (J : BinaryMatrix n) (y : BinaryVector n) :
    applyRowProgram (ops ++ tail) J y =
      applyRowProgram tail (applyRowProgram ops J y).1 (applyRowProgram ops J y).2 := by
  simp [applyRowProgram, List.foldl_append]

theorem pivotPrograms_preserves_prior_unit {n : Nat} (columns : List (Fin n))
    (J : BinaryMatrix n) (old : Fin n) (ops : List (RowOperation n))
    (hlater : ∀ c ∈ columns, old.val < c.val)
    (hunit : ∀ i, J i old = decide (i = old))
    (hprog : pivotPrograms columns J = some ops) :
    ∀ i, (applyRowProgram ops J zeroVector).1 i old = J i old := by
  induction columns generalizing J ops with
  | nil =>
    simp [pivotPrograms] at hprog
    subst ops
    intro i; rfl
  | cons pivot rest ih =>
    have hlt : old.val < pivot.val := hlater pivot (by simp)
    have hrest : ∀ c ∈ rest, old.val < c.val := by
      intro c hc; exact hlater c (by simp [hc])
    simp only [pivotPrograms] at hprog
    cases hf : findPivot J pivot with
    | none => simp [hf] at hprog
    | some row =>
      simp only [hf] at hprog
      let first := RowOperation.swap pivot row :: clearColumnOps (rowSwap J pivot row) pivot
      let next := (applyRowProgram first J zeroVector).1
      cases ht : pivotPrograms rest next with
      | none => simp [first, next, ht] at hprog
      | some tail =>
        have hstep : ∀ i, next i old = J i old := by
          exact pivotStep_preserves_prior_unit J zeroVector old pivot row hlt hf hunit
        have hnextunit : ∀ i, next i old = decide (i = old) := by
          intro i; rw [hstep i, hunit i]
        have htail := ih next tail hrest hnextunit ht
        have heq : ops = first ++ tail := by simpa [first, next, ht] using hprog.symm
        subst ops
        intro i
        rw [rowProgram_append]
        have hind := rowProgram_matrix_independent tail next (applyRowProgram first J zeroVector).2 zeroVector
        change (applyRowProgram tail next (applyRowProgram first J zeroVector).2).1 i old = J i old
        rw [hind]
        exact (htail i).trans (hstep i)

theorem pivotStep_sets_unit {n : Nat} (J : BinaryMatrix n) (y : BinaryVector n)
    (pivot row : Fin n) (hfind : findPivot J pivot = some row) :
    ∀ i, (applyRowProgram (RowOperation.swap pivot row ::
      clearColumnOps (rowSwap J pivot row) pivot) J y).1 i pivot = decide (i = pivot) := by
  have hone : rowSwap J pivot row pivot pivot = true :=
    swap_pivot_entry J pivot row (findPivot_sound J pivot row hfind).2
  intro i
  by_cases hi : i = pivot
  · subst i
    have hp := clearProgram_preserves_pivot (rowSwap J pivot row) (vectorSwap y pivot row) pivot pivot
    simpa [applyRowProgram, applyRowOperation, hone] using hp
  · have hc := clearProgram_clears_column (rowSwap J pivot row) (vectorSwap y pivot row) pivot i hi hone
    simpa [applyRowProgram, applyRowOperation, hi] using hc

theorem pivotPrograms_processed_unit {n : Nat} (columns : List (Fin n))
    (J : BinaryMatrix n) (old : Fin n) (ops : List (RowOperation n))
    (horder : columns.Pairwise (fun a b => a.val < b.val))
    (hmem : old ∈ columns) (hprog : pivotPrograms columns J = some ops) :
    ∀ i, (applyRowProgram ops J zeroVector).1 i old = decide (i = old) := by
  induction columns generalizing J ops with
  | nil => simp at hmem
  | cons pivot rest ih =>
    have hord := List.pairwise_cons.mp horder
    simp only [pivotPrograms] at hprog
    cases hf : findPivot J pivot with
    | none => simp [hf] at hprog
    | some row =>
      simp only [hf] at hprog
      let first := RowOperation.swap pivot row :: clearColumnOps (rowSwap J pivot row) pivot
      let next := (applyRowProgram first J zeroVector).1
      cases ht : pivotPrograms rest next with
      | none => simp [first, next, ht] at hprog
      | some tail =>
        have heq : ops = first ++ tail := by simpa [first, next, ht] using hprog.symm
        subst ops
        have hind := rowProgram_matrix_independent tail next (applyRowProgram first J zeroVector).2 zeroVector
        intro i
        rw [rowProgram_append]
        change (applyRowProgram tail next (applyRowProgram first J zeroVector).2).1 i old = decide (i = old)
        rw [hind]
        by_cases ho : old = pivot
        · subst old
          have hunit : ∀ i, next i pivot = decide (i = pivot) := pivotStep_sets_unit J zeroVector pivot row hf
          have hprior := pivotPrograms_preserves_prior_unit rest next pivot tail hord.1 hunit ht
          exact (hprior i).trans (hunit i)
        · have hm : old ∈ rest := by simpa [ho, Ne.symm ho] using hmem
          exact ih next tail hord.2 hm ht i

theorem gaussianRowProgram_reduces_to_identity {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops) :
    ∀ i k, (applyRowProgram ops J zeroVector).1 i k = decide (i = k) := by
  intro i k
  have horder : (List.finRange n).Pairwise (fun a b => a.val < b.val) := by
    simpa using List.pairwise_lt_finRange n
  exact pivotPrograms_processed_unit (List.finRange n) J k ops horder (List.mem_finRange k) hprog i

end SectorSimulation
