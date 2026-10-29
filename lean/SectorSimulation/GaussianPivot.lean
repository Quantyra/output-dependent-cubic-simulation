import SectorSimulation.MatrixRowProgram
namespace SectorSimulation

def findPivot {n : Nat} (J : BinaryMatrix n) (column : Fin n) : Option (Fin n) :=
  (List.finRange n).find? fun row => decide (column.val ≤ row.val) && J row column

theorem findPivot_sound {n : Nat} (J : BinaryMatrix n) (column row : Fin n)
    (h : findPivot J column = some row) : column.val ≤ row.val ∧ J row column = true := by
  have hp := List.find?_some (p := fun (r : Fin n) => decide (column.val ≤ r.val) && J r column) h
  simpa using hp

theorem findPivot_none {n : Nat} (J : BinaryMatrix n) (column : Fin n)
    (h : findPivot J column = none) :
    ∀ row, column.val ≤ row.val → J row column = false := by
  have hn := List.find?_eq_none.mp h
  intro row hr
  have hp := hn row (List.mem_finRange row)
  simpa [hr] using hp

def clearColumnOps {n : Nat} (J : BinaryMatrix n) (column : Fin n) : List (RowOperation n) :=
  ((List.finRange n).filter fun row => decide (row ≠ column) && J row column).map
    fun row => RowOperation.add row column

def pivotPrograms {n : Nat} : List (Fin n) → BinaryMatrix n → Option (List (RowOperation n))
  | [], _ => some []
  | column :: rest, J =>
    match findPivot J column with
    | none => none
    | some row =>
      let swapped := rowSwap J column row
      let ops := RowOperation.swap column row :: clearColumnOps swapped column
      let reduced := (applyRowProgram ops J zeroVector).1
      (pivotPrograms rest reduced).map (fun tail => ops ++ tail)

def gaussianRowProgram {n : Nat} (J : BinaryMatrix n) : Option (List (RowOperation n)) :=
  pivotPrograms (List.finRange n) J

end SectorSimulation
