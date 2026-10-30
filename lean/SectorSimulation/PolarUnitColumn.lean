import SectorSimulation.PairCross
namespace SectorSimulation

theorem matrixApply_coordinateUnit {n : Nat} (J : BinaryMatrix n) (i : Fin n) :
    matrixApply J (coordinateUnit i) = matrixColumn J i := by
  funext row
  simp only [matrixApply, coordinateUnit, matrixColumn, xorFoldl_as_sum, Bool.false_xor]
  have h : (fun j => J row j && decide (j = i)) =
      (fun j => decide (j = i) && J row j) := by
    funext j; exact Bool.and_comm _ _
  rw [h, booleanListSum_singleton _ i _ (List.nodup_finRange n)]
  simp

theorem sourcePolar_units_are_columns {n : Nat} (p : PhaseANF n) (J : BinaryMatrix n)
    (i j : Fin n) :
    phasePolarFunction (fun x => evalPhase p (matrixApply J x)) (coordinateUnit i) (coordinateUnit j) =
      phasePolar p (matrixColumn J i) (matrixColumn J j) := by
  rw [sourcePolar_matrixChange, matrixApply_coordinateUnit, matrixApply_coordinateUnit]

theorem sourcePolar_recorded_pair_units {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (halt : ∀ x, phasePolar p x x = false)
    (pair : Fin n × Fin n) (hp : pair ∈ (polarEliminate (phasePolar p) fuel indices J).2.2) :
    let out := polarEliminate (phasePolar p) fuel indices J
    phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x))
      (coordinateUnit pair.1) (coordinateUnit pair.2) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit pair.1) (coordinateUnit pair.2) := by
  dsimp only
  rw [sourcePolar_units_are_columns, recordedPairPhase_polar]
  have ha := polarEliminate_all_pairs (phasePolar p) fuel indices J pair hp
  have hd := polarEliminate_distinct_pairs (phasePolar p) fuel indices J halt
  have hb := recordedPairPolar_member_unit _ hd.2 hd.1 pair hp
  rw [ha, hb]
end SectorSimulation
