import SectorSimulation.MatrixRowOperations
namespace SectorSimulation

inductive RowOperation (n : Nat) where
  | swap (a b : Fin n)
  | add (a b : Fin n)

def applyRowOperation {n : Nat} (op : RowOperation n) (J : BinaryMatrix n)
    (y : BinaryVector n) : BinaryMatrix n × BinaryVector n :=
  match op with
  | .swap a b => (rowSwap J a b, vectorSwap y a b)
  | .add a b => if a = b then (J, y) else (rowAdd J a b, vectorAddRow y a b)

theorem applyRowOperation_preserves {n : Nat} (op : RowOperation n) (J : BinaryMatrix n)
    (y x : BinaryVector n) :
    matrixApply (applyRowOperation op J y).1 x = (applyRowOperation op J y).2 ↔
      matrixApply J x = y := by
  cases op with
  | swap a b => exact rowSwap_preserves_solutions J x y a b
  | add a b =>
    by_cases h : a = b
    · simp [applyRowOperation, h]
    · simpa [applyRowOperation, h] using rowAdd_preserves_solutions J x y a b h

def applyRowProgram {n : Nat} (ops : List (RowOperation n)) (J : BinaryMatrix n)
    (y : BinaryVector n) : BinaryMatrix n × BinaryVector n :=
  ops.foldl (fun state op => applyRowOperation op state.1 state.2) (J, y)

theorem applyRowProgram_preserves {n : Nat} (ops : List (RowOperation n)) (J : BinaryMatrix n)
    (y x : BinaryVector n) :
    matrixApply (applyRowProgram ops J y).1 x = (applyRowProgram ops J y).2 ↔
      matrixApply J x = y := by
  induction ops generalizing J y with
  | nil => rfl
  | cons op rest ih =>
    simp only [applyRowProgram, List.foldl_cons]
    cases hs : applyRowOperation op J y with
    | mk J1 y1 =>
      have hp := applyRowOperation_preserves op J y x
      rw [hs] at hp
      exact (ih J1 y1).trans hp

end SectorSimulation
