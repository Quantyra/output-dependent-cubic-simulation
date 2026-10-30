import SectorSimulation.PolarPivot
namespace SectorSimulation

def polarEliminate {n : Nat} (B : BinaryVector n → BinaryVector n → Bool) :
    Nat → List (Fin n) → BinaryMatrix n → BinaryMatrix n × List (Fin n × Fin n) × List (Fin n × Fin n)
  | 0, _, J => (J, [], [])
  | fuel + 1, indices, J =>
    match findPolarPair B J indices with
    | none => (J, [], [])
    | some (u,v) =>
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let step := clearPairColumns B u v rest J
      let result := polarEliminate B fuel rest step.1
      (result.1, step.2 ++ result.2.1, (u,v) :: result.2.2)

theorem polarEliminate_program {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) :
    runColumnAdds (polarEliminate B fuel indices J).2.1 J = (polarEliminate B fuel indices J).1 := by
  induction fuel generalizing indices J with
  | zero => rfl
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp, runColumnAdds]
    | some pair =>
      rcases pair with ⟨u,v⟩
      simp only [polarEliminate, hp]
      rw [show runColumnAdds ((clearPairColumns B u v (indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))) J).2 ++
        (polarEliminate B fuel (indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v)))
          (clearPairColumns B u v (indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))) J).1).2.1) J = _ by
            simp only [runColumnAdds, List.foldl_append]; rfl]
      change runColumnAdds _ (runColumnAdds _ J) = _
      rw [clearPairColumns_program]
      exact ih _ _

theorem polarEliminate_reverse {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) :
    runColumnAdds (polarEliminate B fuel indices J).2.1.reverse (polarEliminate B fuel indices J).1 = J := by
  rw [← polarEliminate_program]
  exact runColumnAdds_reverse_cancels _ _
end SectorSimulation
#print axioms SectorSimulation.polarEliminate_program
#print axioms SectorSimulation.polarEliminate_reverse
