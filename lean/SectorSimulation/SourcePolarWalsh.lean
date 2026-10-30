import SectorSimulation.PolarBasis
import SectorSimulation.SourceWalshReindex
namespace SectorSimulation

theorem sourceWalshSum_polar_reindex {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (indices : List (Fin n)) :
    let J := (polarEliminate (phasePolar p) fuel indices identityMatrix).1
    sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor (evalPhase p (matrixApply J y))
        (walshWireParity (List.finRange n) l (matrixApply J y))))).sum := by
  have hid : Function.Injective (matrixApply (identityMatrix : BinaryMatrix n)) := by
    intro x y h
    simpa [matrixApply_identity] using h
  obtain ⟨ops, hop⟩ := polarEliminate_gaussian_program (phasePolar p) fuel indices identityMatrix hid
  exact sourceWalshSum_reindex p l _ ops hop
end SectorSimulation
