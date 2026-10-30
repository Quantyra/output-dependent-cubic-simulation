import SectorSimulation.PolarFuel
namespace SectorSimulation

def unpairedIndices {n : Nat} (indices : List (Fin n)) (pairs : List (Fin n × Fin n)) : List (Fin n) :=
  indices.filter fun i => !(pairs.any fun p => decide (i = p.1) || decide (i = p.2))

theorem polarEliminate_residual_zero {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) (hbound : indices.length ≤ fuel) :
    ∀ u ∈ unpairedIndices indices (polarEliminate B fuel indices J).2.2,
    ∀ v ∈ unpairedIndices indices (polarEliminate B fuel indices J).2.2,
      B (matrixColumn (polarEliminate B fuel indices J).1 u)
        (matrixColumn (polarEliminate B fuel indices J).1 v) = false := by
  induction fuel generalizing indices J with
  | zero =>
    cases indices with
    | nil => simp [unpairedIndices]
    | cons a rest => simp at hbound
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none =>
      have hn := findPolarPair_none B J indices hp
      simp only [polarEliminate, hp]
      intro u hu v hv
      exact hn u (by simpa [unpairedIndices] using hu) v (by simpa [unpairedIndices] using hv)
    | some pair =>
      rcases pair with ⟨a,b⟩
      have ha := (findPolarPair_sound B J indices a b hp).1
      let rest := indices.filter (fun i => decide (i ≠ a) && decide (i ≠ b))
      let next := (clearPairColumns B a b rest J).1
      have hlt : rest.length < indices.length := by
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨a, ha, by simp⟩
      have hr : rest.length ≤ fuel := by omega
      have hrec := ih rest next hr
      simp only [polarEliminate, hp]
      intro u hu v hv
      apply hrec u _ v _
      · simpa [unpairedIndices, rest, next, and_assoc, and_comm, and_left_comm] using hu
      · simpa [unpairedIndices, rest, next, and_assoc, and_comm, and_left_comm] using hv
end SectorSimulation
#print axioms SectorSimulation.polarEliminate_residual_zero
