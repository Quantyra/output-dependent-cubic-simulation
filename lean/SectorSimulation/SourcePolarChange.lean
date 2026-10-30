import SectorSimulation.AffineCoordinates
import SectorSimulation.SourcePolarWalsh
namespace SectorSimulation

theorem sourcePolar_matrixChange {n : Nat} (p : PhaseANF n) (J : BinaryMatrix n)
    (u v : BinaryVector n) :
    phasePolarFunction (fun x => evalPhase p (matrixApply J x)) u v =
      phasePolar p (matrixApply J u) (matrixApply J v) := by
  have hx : matrixApply J (binaryShift u v) = binaryShift (matrixApply J u) (matrixApply J v) := by
    simpa [binaryShift, vectorXor] using matrixApply_xor J v u
  have hz : matrixApply J (fun _ => false) = (fun _ => false) := matrixApply_zero J
  simp only [phasePolarFunction, phasePolar, hx, hz]

theorem sourceMatrix_equalPolar_affine {n : Nat} (p : PhaseANF n) (J : BinaryMatrix n)
    (r : BinaryVector n → Bool)
    (hpolar : ∀ u v, phasePolar p (matrixApply J u) (matrixApply J v) = phasePolarFunction r u v)
    (x : BinaryVector n) :
    Bool.xor (evalPhase p (matrixApply J x)) (r x) =
      Bool.xor (Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false)))
        (walshWireParity (List.finRange n)
          (fun i => normalizedDifference (fun y => evalPhase p (matrixApply J y)) r (coordinateUnit i)) x) := by
  have hp : ∀ u v, phasePolarFunction (fun y => evalPhase p (matrixApply J y)) u v = phasePolarFunction r u v := by
    intro u v; rw [sourcePolar_matrixChange]; exact hpolar u v
  have h := samePolar_affine_coordinates (fun y => evalPhase p (matrixApply J y)) r hp x
  have hz : matrixApply J (fun _ => false) = (fun _ => false) := matrixApply_zero J
  rw [hz] at h
  exact h
end SectorSimulation
