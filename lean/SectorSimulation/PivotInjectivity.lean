import SectorSimulation.PivotSolveCorrect
namespace SectorSimulation

theorem rowProgram_preserves_injective {n : Nat} (ops : List (RowOperation n))
    (J : BinaryMatrix n) (y : BinaryVector n)
    (hinj : ∀ x z, matrixApply J x = matrixApply J z → x = z) :
    ∀ x z, matrixApply (applyRowProgram ops J y).1 x =
      matrixApply (applyRowProgram ops J y).1 z → x = z := by
  intro x z heq
  let target := matrixApply J z
  have hsolz := (applyRowProgram_preserves ops J target z).mpr rfl
  have hind := rowProgram_matrix_independent ops J y target
  have hsolx : matrixApply (applyRowProgram ops J target).1 x = (applyRowProgram ops J target).2 := by
    rw [← hind]
    have hz : matrixApply (applyRowProgram ops J y).1 z = (applyRowProgram ops J target).2 := by
      rw [hind]; exact hsolz
    exact heq.trans hz
  have horig := (applyRowProgram_preserves ops J target x).mp hsolx
  exact hinj x z horig

theorem successfulProgram_injective {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops) :
    ∀ x z, matrixApply J x = matrixApply J z → x = z := by
  intro x z heq
  let target := matrixApply J x
  have hx := (applyRowProgram_preserves ops J target x).mpr rfl
  have hz := (applyRowProgram_preserves ops J target z).mpr heq.symm
  have hind := rowProgram_matrix_independent ops J target zeroVector
  have hmat : (applyRowProgram ops J target).1 = identityMatrix := by
    rw [hind]
    funext i k
    exact gaussianRowProgram_reduces_to_identity J ops hprog i k
  rw [hmat, matrixApply_identity] at hx hz
  exact hx.trans hz.symm

end SectorSimulation
