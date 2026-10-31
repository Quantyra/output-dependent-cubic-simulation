import SectorSimulation.CoordinateInverse
namespace SectorSimulation

theorem sourceWalshSum_recorded_inverse_reindex {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hd : ∀ q ∈ (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2, q.1 ≠ q.2)
    (hp : ((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).Pairwise pairDisjoint) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let hlen : (recordedCoordinateOrder out.2.2).length = n := by
      simpa using (recordedCoordinateOrder_perm out.2.2 hd hp).length_eq
    let f := recordedCoordinateAt out.2.2 hlen
    let fsurj := (recordedCoordinateAt_bijective out.2.2 hd hp).2
    let inv := coordinateInverse f fsurj
    let r := fun x => evalPhase (recordedPairPhase out.2.2) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor c (Bool.xor (r (coordinateReindex inv y))
        (walshWireParity (List.finRange n) t (coordinateReindex inv y)))))).sum := by
  dsimp only
  rw [sourceWalshSum_recorded_character p l fuel hdegree hbound]
  apply coordinateReindex_sum
  · exact (coordinateInverse_bijective _ (recordedCoordinateAt_bijective _ hd hp).1 (recordedCoordinateAt_bijective _ hd hp).2).1
  · exact (coordinateInverse_bijective _ (recordedCoordinateAt_bijective _ hd hp).1 (recordedCoordinateAt_bijective _ hd hp).2).2


end SectorSimulation