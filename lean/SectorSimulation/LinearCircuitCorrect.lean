import SectorSimulation.LinearGateSemantics
import SectorSimulation.PivotSolveCorrect
namespace SectorSimulation

def validCNOTs {n : Nat} (gates : List (CNOTRecord n)) : Prop :=
  ∀ g ∈ gates, g.1 ≠ g.2

theorem rowOperationCNOTs_valid {n : Nat} (op : RowOperation n) :
    validCNOTs (rowOperationCNOTs op) := by
  cases op with
  | swap a b =>
    by_cases h : a = b
    · simp [validCNOTs, rowOperationCNOTs, h]
    · simp [validCNOTs, rowOperationCNOTs, h, Ne.symm h]
  | add a b =>
    by_cases h : a = b
    · simp [validCNOTs, rowOperationCNOTs, h]
    · simp [validCNOTs, rowOperationCNOTs, h, Ne.symm h]

theorem rowProgramCNOTs_valid {n : Nat} (ops : List (RowOperation n)) :
    validCNOTs (rowProgramCNOTs ops) := by
  intro g hg
  obtain ⟨op, hop, hgate⟩ := List.mem_flatMap.mp hg
  exact rowOperationCNOTs_valid op g hgate

theorem runCNOTs_reverse_cancels {n : Nat} (gates : List (CNOTRecord n))
    (x : BinaryVector n) (hvalid : validCNOTs gates) :
    runCNOTs gates.reverse (runCNOTs gates x) = x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have hg : g.1 ≠ g.2 := hvalid g (by simp)
    have hr : validCNOTs rest := by
      intro gate hm
      exact hvalid gate (by simp [hm])
    simp only [List.reverse_cons, runCNOTs, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change applyCNOT g.1 g.2 (runCNOTs rest.reverse (runCNOTs rest (applyCNOT g.1 g.2 x))) = x
    rw [ih _ hr]
    exact CNOT_involutive g.1 g.2 x (Ne.symm hg)

theorem gaussianCNOTs_forward_inverse {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (x : BinaryVector n) :
    runCNOTs (rowProgramCNOTs ops) (matrixApply J x) = x := by
  rw [rowProgramCNOTs_correct]
  have hpres := (applyRowProgram_preserves ops J (matrixApply J x) x).mpr rfl
  have hind := rowProgram_matrix_independent ops J (matrixApply J x) zeroVector
  have hmat : (applyRowProgram ops J (matrixApply J x)).1 = identityMatrix := by
    rw [hind]
    funext i k
    exact gaussianRowProgram_reduces_to_identity J ops hprog i k
  rw [hmat, matrixApply_identity] at hpres
  exact hpres.symm

theorem gaussianCNOTs_reversed_implements_matrix {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (x : BinaryVector n) :
    runCNOTs (rowProgramCNOTs ops).reverse x = matrixApply J x := by
  have h := runCNOTs_reverse_cancels (rowProgramCNOTs ops) (matrixApply J x)
    (rowProgramCNOTs_valid ops)
  rw [gaussianCNOTs_forward_inverse J ops hprog x] at h
  exact h

end SectorSimulation
