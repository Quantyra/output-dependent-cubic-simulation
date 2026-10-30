import SectorSimulation.PolarResidualPair
namespace SectorSimulation

theorem polarEliminate_normal_certificate {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (halt : ∀ x, B x x = false) (hsym : ∀ x y, B x y = B y x)
    (hn : indices.Nodup) (hbound : indices.length ≤ fuel) :
    let result := polarEliminate B fuel indices J
    runColumnAdds result.2.1 J = result.1 ∧
    runColumnAdds result.2.1.reverse result.1 = J ∧
    (∀ p ∈ result.2.2, p.1 ∈ indices ∧ p.2 ∈ indices) ∧
    (∀ p ∈ result.2.2, p.1 ≠ p.2) ∧
    result.2.2.Pairwise pairDisjoint ∧
    (∀ p ∈ result.2.2, B (matrixColumn result.1 p.1) (matrixColumn result.1 p.2) = true) ∧
    result.2.2.Pairwise (pairOrthogonal B result.1) ∧
    (∀ u ∈ unpairedIndices indices result.2.2, ∀ v ∈ unpairedIndices indices result.2.2,
      B (matrixColumn result.1 u) (matrixColumn result.1 v) = false) ∧
    (∀ t ∈ unpairedIndices indices result.2.2, ∀ p ∈ result.2.2,
      B (matrixColumn result.1 t) (matrixColumn result.1 p.1) = false ∧
      B (matrixColumn result.1 t) (matrixColumn result.1 p.2) = false) := by
  exact ⟨polarEliminate_program B fuel indices J, polarEliminate_reverse B fuel indices J,
    polarEliminate_pair_members B fuel indices J, (polarEliminate_distinct_pairs B fuel indices J halt).1,
    (polarEliminate_distinct_pairs B fuel indices J halt).2,
    polarEliminate_all_pairs B fuel indices J,
    polarEliminate_pairwise_orthogonal B fuel indices J hadd hzero halt hsym hn,
    polarEliminate_residual_zero B fuel indices J hbound,
    polarEliminate_residual_pair_orthogonal B fuel indices J hadd hzero halt hsym hn⟩

end SectorSimulation
