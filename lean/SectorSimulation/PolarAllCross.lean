import SectorSimulation.PolarFirstCross
namespace SectorSimulation

theorem polarEliminate_pair_members {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) :
    ∀ p ∈ (polarEliminate B fuel indices J).2.2, p.1 ∈ indices ∧ p.2 ∈ indices := by
  induction fuel generalizing indices J with
  | zero => simp [polarEliminate]
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      have hs := findPolarPair_sound B J indices u v hp
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have hr := ih rest next
      simp only [polarEliminate, hp]
      intro p hm
      simp only [List.mem_cons] at hm
      rcases hm with he | ht
      · subst p; exact ⟨hs.1, hs.2.1⟩
      · have hh := hr p ht
        exact ⟨(List.mem_filter.mp hh.1).1, (List.mem_filter.mp hh.2).1⟩

def pairOrthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (p q : Fin n × Fin n) : Prop :=
  B (matrixColumn J q.1) (matrixColumn J p.1) = false ∧
  B (matrixColumn J q.1) (matrixColumn J p.2) = false ∧
  B (matrixColumn J q.2) (matrixColumn J p.1) = false ∧
  B (matrixColumn J q.2) (matrixColumn J p.2) = false

theorem polarEliminate_pairwise_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (halt : ∀ x, B x x = false) (hsym : ∀ x y, B x y = B y x)
    (hn : indices.Nodup) :
    ((polarEliminate B fuel indices J).2.2).Pairwise
      (pairOrthogonal B (polarEliminate B fuel indices J).1) := by
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
      have htail := ih rest next hnr
      have hmembers := polarEliminate_pair_members B fuel rest next
      have hfirst := polarEliminate_first_orthogonal B fuel indices J u v hadd hzero halt hsym hn hp
      simp only [polarEliminate, hp]
      apply List.pairwise_cons.mpr
      constructor
      · intro q hq
        have hm := hmembers q hq
        have hq1 := List.mem_filter.mp hm.1
        have hq2 := List.mem_filter.mp hm.2
        have hq1ne : q.1 ≠ u ∧ q.1 ≠ v := by simpa using hq1.2
        have h1 := hfirst q.1 hq1.1 hq1ne.1 hq1ne.2
        have hq2ne : q.2 ≠ u ∧ q.2 ≠ v := by simpa using hq2.2
        have h2 := hfirst q.2 hq2.1 hq2ne.1 hq2ne.2
        simpa [pairOrthogonal, polarEliminate, hp, rest, next, and_assoc] using And.intro h1 h2
      · exact htail
end SectorSimulation
