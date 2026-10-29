import SectorSimulation.GaussianPivotSize
namespace SectorSimulation

def gaussianSolveChecked {n : Nat} (J : BinaryMatrix n) (target : BinaryVector n) : Option (BinaryVector n) :=
  match gaussianRowProgram J with
  | none => none
  | some ops =>
    let candidate := (applyRowProgram ops J target).2
    if vectorEqual (matrixApply J candidate) target then some candidate else none

theorem gaussianSolveChecked_sound {n : Nat} (J : BinaryMatrix n) (target x : BinaryVector n)
    (h : gaussianSolveChecked J target = some x) : matrixApply J x = target := by
  unfold gaussianSolveChecked at h
  cases hp : gaussianRowProgram J with
  | none => simp [hp] at h
  | some ops =>
    simp only [hp] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst x
      exact (vectorEqual_correct _ _).mp hv
    · contradiction

end SectorSimulation
