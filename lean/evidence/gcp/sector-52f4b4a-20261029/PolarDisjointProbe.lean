import SectorSimulation.PolarAllCross
namespace SectorSimulation

def pairDisjoint {n : Nat} (p q : Fin n × Fin n) : Prop :=
  q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2

theorem polarEliminate_distinct_pairs {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (halt : ∀ x, B x x = false) :
    (∀ p ∈ (polarEliminate B fuel indices J).2.2, p.1 ≠ p.2) ∧
    ((polarEliminate B fuel indices J).2.2).Pairwise pairDisjoint := by
  induction fuel generalizing indices J with
  | zero => simp [polarEliminate]
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have huv := findPolarPair_distinct B J indices u v halt hp
      have htail := ih rest next
      have hmem := polarEliminate_pair_members B fuel rest next
      simp only [polarEliminate, hp]
      constructor
      · intro p hm
        simp only [List.mem_cons] at hm
        rcases hm with he | ht
        · subst p; exact huv
        · exact htail.1 p ht
      · apply List.pairwise_cons.mpr
        constructor
        · intro q hq
          have hm := hmem q hq
          have h1 := (List.mem_filter.mp hm.1).2
          have h2 := (List.mem_filter.mp hm.2).2
          have h1ne : q.1 ≠ u ∧ q.1 ≠ v := by simpa using h1
          have h2ne : q.2 ≠ u ∧ q.2 ≠ v := by simpa using h2
          exact ⟨h1ne.1, h1ne.2, h2ne.1, h2ne.2⟩
        · exact htail.2
end SectorSimulation
#print axioms SectorSimulation.polarEliminate_distinct_pairs
