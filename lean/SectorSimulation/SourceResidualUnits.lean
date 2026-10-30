import SectorSimulation.PolarUnitColumn
namespace SectorSimulation

theorem unpairedIndices_absent {n : Nat} (indices : List (Fin n))
    (pairs : List (Fin n × Fin n)) (i : Fin n)
    (hi : i ∈ unpairedIndices indices pairs) :
    ∀ p ∈ pairs, i ≠ p.1 ∧ i ≠ p.2 := by
  simp [unpairedIndices] at hi
  intro pair hp
  rcases pair with ⟨a,b⟩
  exact hi.2 a b hp

theorem sourcePolar_residual_units {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hbound : indices.length ≤ fuel) (i j : Fin n)
    (hi : i ∈ unpairedIndices indices (polarEliminate (phasePolar p) fuel indices J).2.2)
    (hj : j ∈ unpairedIndices indices (polarEliminate (phasePolar p) fuel indices J).2.2) :
    let out := polarEliminate (phasePolar p) fuel indices J
    phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit i) (coordinateUnit j) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit i) (coordinateUnit j) := by
  dsimp only
  rw [sourcePolar_units_are_columns, recordedPairPhase_polar]
  have ha := polarEliminate_residual_zero (phasePolar p) fuel indices J hbound i hi j hj
  have hb := recordedPairPolar_unit_absent _ i j (unpairedIndices_absent indices _ i hi)
  rw [ha, hb]
end SectorSimulation
