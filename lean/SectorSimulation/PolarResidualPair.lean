import SectorSimulation.PolarDisjoint
namespace SectorSimulation

theorem polarEliminate_residual_pair_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (halt : ∀ x, B x x = false) (hsym : ∀ x y, B x y = B y x)
    (hn : indices.Nodup) :
    ∀ t ∈ unpairedIndices indices (polarEliminate B fuel indices J).2.2,
    ∀ p ∈ (polarEliminate B fuel indices J).2.2,
      B (matrixColumn (polarEliminate B fuel indices J).1 t)
        (matrixColumn (polarEliminate B fuel indices J).1 p.1) = false ∧
      B (matrixColumn (polarEliminate B fuel indices J).1 t)
        (matrixColumn (polarEliminate B fuel indices J).1 p.2) = false := by
  induction fuel generalizing indices J with
  | zero => simp [polarEliminate]
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have hnr : rest.Nodup := List.Nodup.sublist List.filter_sublist hn
      have hrec := ih rest next hnr
      have hfirst := polarEliminate_first_orthogonal B fuel indices J u v hadd hzero halt hsym hn hp
      simp only [polarEliminate, hp]
      intro t ht p hpairs
      have htparts : t ∈ indices ∧ t ≠ u ∧ t ≠ v ∧
          t ∈ unpairedIndices rest (polarEliminate B fuel rest next).2.2 := by
        simpa [unpairedIndices, rest, next, and_assoc, and_comm, and_left_comm] using ht
      simp only [List.mem_cons] at hpairs
      rcases hpairs with he | hm
      · subst p
        simpa [polarEliminate, hp, rest, next] using hfirst t htparts.1 htparts.2.1 htparts.2.2.1
      · exact hrec t htparts.2.2.2 p hm
end SectorSimulation
