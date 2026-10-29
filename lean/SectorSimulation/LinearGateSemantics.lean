import SectorSimulation.PivotProgramCorrect
import SectorSimulation.NativeGateHeader
namespace SectorSimulation

/-- Classical basis action of a distinct-wire controlled-NOT. -/
def applyCNOT {n : Nat} (control target : Fin n) (x : BinaryVector n) : BinaryVector n :=
  vectorAddRow x target control

/-- The three CNOTs used by the native linear compiler implement a swap. -/
theorem threeCNOT_swap {n : Nat} (a b : Fin n) (x : BinaryVector n) (h : a ≠ b) :
    applyCNOT a b (applyCNOT b a (applyCNOT a b x)) = vectorSwap x a b := by
  funext i
  by_cases ha : i = a
  · subst i
    simp only [applyCNOT, vectorAddRow, vectorSwap, if_neg h, if_neg (Ne.symm h)]
    cases x a <;> cases x b <;> rfl
  · by_cases hb : i = b
    · subst i
      simp only [applyCNOT, vectorAddRow, vectorSwap, if_neg h, if_neg (Ne.symm h)]
      cases x a <;> cases x b <;> rfl
    · simp [applyCNOT, vectorAddRow, vectorSwap, ha, hb]

/-- A distinct-wire CNOT is its own inverse on every basis vector. -/
theorem CNOT_involutive {n : Nat} (control target : Fin n) (x : BinaryVector n)
    (h : target ≠ control) : applyCNOT control target (applyCNOT control target x) = x := by
  exact vectorAddRow_involutive x target control h

/-- Native CNOT records, with control first and target second. -/
abbrev CNOTRecord (n : Nat) := Fin n × Fin n

def rowOperationCNOTs {n : Nat} : RowOperation n → List (CNOTRecord n)
  | .swap a b => if a = b then [] else [(a,b), (b,a), (a,b)]
  | .add target control => if target = control then [] else [(control,target)]

def runCNOTs {n : Nat} (gates : List (CNOTRecord n)) (x : BinaryVector n) : BinaryVector n :=
  gates.foldl (fun state gate => applyCNOT gate.1 gate.2 state) x

theorem rowOperationCNOTs_correct {n : Nat} (op : RowOperation n)
    (J : BinaryMatrix n) (x : BinaryVector n) :
    runCNOTs (rowOperationCNOTs op) x = (applyRowOperation op J x).2 := by
  cases op with
  | swap a b =>
    by_cases h : a = b
    · subst b
      funext i
      by_cases hi : i = a <;> simp [rowOperationCNOTs, runCNOTs, applyRowOperation, vectorSwap, hi]
    · simpa [rowOperationCNOTs, runCNOTs, applyRowOperation, h] using threeCNOT_swap a b x h
  | add target control =>
    by_cases h : target = control
    · simp [rowOperationCNOTs, runCNOTs, applyRowOperation, h]
    · simp [rowOperationCNOTs, runCNOTs, applyRowOperation, applyCNOT, h]

def rowProgramCNOTs {n : Nat} (ops : List (RowOperation n)) : List (CNOTRecord n) :=
  ops.flatMap rowOperationCNOTs

theorem rowProgramCNOTs_correct {n : Nat} (ops : List (RowOperation n))
    (J : BinaryMatrix n) (x : BinaryVector n) :
    runCNOTs (rowProgramCNOTs ops) x = (applyRowProgram ops J x).2 := by
  induction ops generalizing J x with
  | nil => rfl
  | cons op rest ih =>
    simp only [rowProgramCNOTs, List.flatMap_cons, runCNOTs, List.foldl_append]
    change runCNOTs (rowProgramCNOTs rest) (runCNOTs (rowOperationCNOTs op) x) = _
    rw [rowOperationCNOTs_correct op J x]
    simpa [applyRowProgram, List.foldl_cons] using ih (applyRowOperation op J x).1 (applyRowOperation op J x).2

end SectorSimulation
