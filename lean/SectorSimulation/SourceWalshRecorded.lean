import SectorSimulation.SourceRecordedAffine
namespace SectorSimulation

theorem sourceWalshSum_recorded_affine {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let r := fun x => evalPhase (recordedPairPhase out.2.2) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor (Bool.xor (r y) (Bool.xor c (walshWireParity (List.finRange n) a y)))
        (walshWireParity (List.finRange n) l (matrixApply out.1 y))))).sum := by
  dsimp only
  rw [sourceWalshSum_polar_reindex p l fuel (List.finRange n)]
  congr 2
  funext y
  have h := sourcePolar_recorded_affine p fuel identityMatrix hdegree hbound y
  dsimp only at h
  have hx : ∀ a b c : Bool, Bool.xor a b = c → a = Bool.xor b c := by
    intro a b c h; cases a <;> cases b <;> cases c <;> simp_all
  rw [hx _ _ _ h]


end SectorSimulation