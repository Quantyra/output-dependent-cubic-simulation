import SectorSimulation.PairwiseSymmetric
namespace SectorSimulation

theorem disjoint_pairs_unrelated_first {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (p q : Fin n × Fin n)
    (hp : p ∈ pairs) (hq : q ∈ pairs) (hne : p ≠ q) :
    ∀ r ∈ pairs, ¬ ((q.1 = r.1 ∧ p.1 = r.2) ∨ (q.1 = r.2 ∧ p.1 = r.1)) := by
  have hpq := pairwise_symmetric_members pairDisjoint pairDisjoint_symmetric pairs hd p q hp hq hne
  intro r hr
  by_cases h : p = r
  · subst r
    simp_all [pairDisjoint, eq_comm]
  · have hpr := pairwise_symmetric_members pairDisjoint pairDisjoint_symmetric pairs hd p r hp hr h
    simp_all [pairDisjoint, eq_comm]

theorem sourcePolar_cross_first_units {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, phasePolar p (binaryShift a b) z = Bool.xor (phasePolar p a z) (phasePolar p b z))
    (hzero : ∀ z, phasePolar p (fun _ => false) z = false)
    (halt : ∀ x, phasePolar p x x = false) (hsym : ∀ x y, phasePolar p x y = phasePolar p y x)
    (hn : indices.Nodup) (a b : Fin n × Fin n)
    (ha : a ∈ (polarEliminate (phasePolar p) fuel indices J).2.2)
    (hb : b ∈ (polarEliminate (phasePolar p) fuel indices J).2.2) (hne : a ≠ b) :
    let out := polarEliminate (phasePolar p) fuel indices J
    phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit b.1) (coordinateUnit a.1) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit b.1) (coordinateUnit a.1) := by
  dsimp only
  rw [sourcePolar_units_are_columns, recordedPairPhase_polar]
  have ho := polarEliminate_pairwise_orthogonal (phasePolar p) fuel indices J hadd hzero halt hsym hn
  have hd := (polarEliminate_distinct_pairs (phasePolar p) fuel indices J halt).2
  have hab := pairwise_symmetric_members _ (pairOrthogonal_symmetric _ _ hsym) _ ho a b ha hb hne
  have hc := recordedPairPolar_unit_unrelated _ b.1 a.1 (disjoint_pairs_unrelated_first _ hd a b ha hb hne)
  exact hab.1.trans hc.symm
end SectorSimulation
