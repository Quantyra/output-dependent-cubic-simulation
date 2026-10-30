import SectorSimulation.PolarEliminate
namespace SectorSimulation

theorem polarEliminate_fuel_stable {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hbound : indices.length ≤ fuel) :
    polarEliminate B (fuel + 1) indices J = polarEliminate B fuel indices J := by
  induction fuel generalizing indices J with
  | zero =>
    cases indices with
    | nil => rfl
    | cons a tail => simp at hbound
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      have hu := (findPolarPair_sound B J indices u v hp).1
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      have hlt : rest.length < indices.length := by
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨u, hu, by simp⟩
      have hr : rest.length ≤ fuel := by omega
      have hrec := ih rest (clearPairColumns B u v rest J).1 hr
      conv =>
        lhs
        rw [polarEliminate, hp]
      conv =>
        rhs
        rw [polarEliminate, hp]
      dsimp only
      rw [hrec]
end SectorSimulation
