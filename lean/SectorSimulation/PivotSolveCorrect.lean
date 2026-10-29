import SectorSimulation.PivotProgramCorrect
namespace SectorSimulation

def identityMatrix {n : Nat} : BinaryMatrix n := fun i k => decide (i = k)

theorem identityFold_absent {n : Nat} (xs : List (Fin n)) (i : Fin n) (x : BinaryVector n)
    (initial : Bool) (h : i ∉ xs) :
    xs.foldl (fun acc k => Bool.xor acc (decide (i = k) && x k)) initial = initial := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hn : i ≠ a := by intro he; subst a; exact h (by simp)
    have hr : i ∉ rest := by intro hm; exact h (by simp [hm])
    simp [hn, ih hr]

theorem identityFold_present {n : Nat} (xs : List (Fin n)) (i : Fin n) (x : BinaryVector n)
    (hn : xs.Nodup) (hm : i ∈ xs) :
    xs.foldl (fun acc k => Bool.xor acc (decide (i = k) && x k)) false = x i := by
  induction xs with
  | nil => simp at hm
  | cons a rest ih =>
    have hd := List.nodup_cons.mp hn
    by_cases he : i = a
    · subst a
      simp only [List.foldl_cons, decide_true, Bool.true_and, Bool.false_xor]
      exact identityFold_absent rest i x (x i) hd.1
    · have hr : i ∈ rest := by simpa [he, Ne.symm he] using hm
      simpa [he] using ih hd.2 hr

theorem matrixApply_identity {n : Nat} (x : BinaryVector n) : matrixApply identityMatrix x = x := by
  funext i
  exact identityFold_present (List.finRange n) i x (List.nodup_finRange n) (List.mem_finRange i)

theorem successfulProgram_solves_all_targets {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (target : BinaryVector n) :
    matrixApply J (applyRowProgram ops J target).2 = target := by
  have hind := rowProgram_matrix_independent ops J target zeroVector
  have hmat : (applyRowProgram ops J target).1 = identityMatrix := by
    rw [hind]
    funext i k
    exact gaussianRowProgram_reduces_to_identity J ops hprog i k
  have hsolution : matrixApply (applyRowProgram ops J target).1
      (applyRowProgram ops J target).2 = (applyRowProgram ops J target).2 := by
    rw [hmat, matrixApply_identity]
  exact (applyRowProgram_preserves ops J target (applyRowProgram ops J target).2).mp hsolution

theorem gaussianSolveChecked_returns_of_program {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (target : BinaryVector n) :
    gaussianSolveChecked J target = some (applyRowProgram ops J target).2 := by
  have hsol := successfulProgram_solves_all_targets J ops hprog target
  have hcheck := (vectorEqual_correct _ _).mpr hsol
  simp [gaussianSolveChecked, hprog, hcheck]

end SectorSimulation
