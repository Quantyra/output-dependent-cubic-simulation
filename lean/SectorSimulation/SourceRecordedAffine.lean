import SectorSimulation.SourcePolarAll
namespace SectorSimulation

theorem sourcePolar_recorded_affine {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (J : BinaryMatrix n)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (x : BinaryVector n) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) J
    Bool.xor (evalPhase p (matrixApply out.1 x)) (evalPhase (recordedPairPhase out.2.2) x) =
      Bool.xor (Bool.xor (evalPhase p (fun _ => false)) (evalPhase (recordedPairPhase out.2.2) (fun _ => false)))
        (walshWireParity (List.finRange n)
          (fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y))
            (fun y => evalPhase (recordedPairPhase out.2.2) y) (coordinateUnit i)) x) := by
  dsimp only
  apply sourceMatrix_equalPolar_affine
  intro u v
  exact sourcePolar_all_vectors p fuel J hdegree hbound u v


end SectorSimulation