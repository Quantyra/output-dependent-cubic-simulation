import SectorSimulation.SourceResidualUnits
namespace SectorSimulation

theorem sourcePolar_residual_pair_units {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, phasePolar p (binaryShift a b) z = Bool.xor (phasePolar p a z) (phasePolar p b z))
    (hzero : ∀ z, phasePolar p (fun _ => false) z = false)
    (halt : ∀ x, phasePolar p x x = false) (hsym : ∀ x y, phasePolar p x y = phasePolar p y x)
    (hn : indices.Nodup) (i : Fin n) (pair : Fin n × Fin n)
    (hi : i ∈ unpairedIndices indices (polarEliminate (phasePolar p) fuel indices J).2.2)
    (hp : pair ∈ (polarEliminate (phasePolar p) fuel indices J).2.2) :
    let out := polarEliminate (phasePolar p) fuel indices J
    (phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit i) (coordinateUnit pair.1) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit i) (coordinateUnit pair.1)) ∧
    (phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit i) (coordinateUnit pair.2) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit i) (coordinateUnit pair.2)) := by
  dsimp only
  simp only [sourcePolar_units_are_columns, recordedPairPhase_polar]
  have ha := polarEliminate_residual_pair_orthogonal (phasePolar p) fuel indices J hadd hzero halt hsym hn i hi pair hp
  have habs := unpairedIndices_absent indices _ i hi
  have hb1 := recordedPairPolar_unit_absent _ i pair.1 habs
  have hb2 := recordedPairPolar_unit_absent _ i pair.2 habs
  exact ⟨ha.1.trans hb1.symm, ha.2.trans hb2.symm⟩
end SectorSimulation
