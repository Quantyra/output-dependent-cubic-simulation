import SectorSimulation.SourceWalshRecorded
import SectorSimulation.BinaryTransposeCharacter
import SectorSimulation.MatrixPairing
namespace SectorSimulation

theorem sourceWalshSum_recorded_character {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let r := fun x => evalPhase (recordedPairPhase out.2.2) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor c (Bool.xor (r y) (walshWireParity (List.finRange n) t y))))).sum := by
  dsimp only
  rw [sourceWalshSum_recorded_affine p l fuel hdegree hbound]
  congr 2
  funext y
  rw [binaryTranspose_character]
  rw [walshWireParity_comm _ (binaryShift _ _) y, walshWireParity_shift,
    walshWireParity_comm _ y, walshWireParity_comm _ y]
  congr 1
  simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]


end SectorSimulation