import SectorSimulation.SourceInverseReindex
namespace SectorSimulation

theorem sourceWalshSum_inverse_layout {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    ∃ f g : Fin n → Fin n, Function.Injective f ∧ (∀ x, ∃ i, f i = x) ∧
      (∀ y i, coordinateReindex g y (f i) = y i) ∧
      let r := fun x => evalPhase (recordedPairPhase out.2.2) x
      let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
      let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
      let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
      sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
        (Bool.xor c (Bool.xor (r (coordinateReindex g y))
          (walshWireParity (List.finRange n) t (coordinateReindex g y)))))).sum := by
  dsimp only
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl : ∀ x, phasePolar p x x = false := by intro x; rw [hpolar]; exact halt x
  have hd := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl
  let pairs := (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
  have hlen : (recordedCoordinateOrder pairs).length = n := by
    simpa using (recordedCoordinateOrder_perm pairs hd.1 hd.2).length_eq
  let f := recordedCoordinateAt pairs hlen
  have hb := recordedCoordinateAt_bijective pairs hd.1 hd.2
  refine ⟨f, coordinateInverse f hb.2, hb.1, hb.2, ?_, ?_⟩
  · exact coordinateReindex_inverse_at f hb.1 hb.2
  · exact sourceWalshSum_recorded_inverse_reindex p l fuel hdegree hbound hd.1 hd.2


end SectorSimulation