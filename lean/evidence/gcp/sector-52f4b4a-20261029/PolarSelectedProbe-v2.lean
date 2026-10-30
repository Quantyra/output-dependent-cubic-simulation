import SectorSimulation.PolarResidual
namespace SectorSimulation

theorem polarEliminate_other {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) (j : Fin n)
    (hj : j ∉ indices) :
    matrixColumn (polarEliminate B fuel indices J).1 j = matrixColumn J j := by
  induction fuel generalizing indices J with
  | zero => rfl
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      have hjr : j ∉ rest := by simp [rest, hj]
      have hs := clearPairColumns_other B u v j rest J hjr
      have hi := ih rest (clearPairColumns B u v rest J).1 hjr
      simp only [polarEliminate, hp]
      exact hi.trans hs

theorem polarEliminate_first_pair {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) (u v : Fin n)
    (hp : findPolarPair B J indices = some (u,v)) :
    B (matrixColumn (polarEliminate B (fuel+1) indices J).1 u)
      (matrixColumn (polarEliminate B (fuel+1) indices J).1 v) = true := by
  have huv := (findPolarPair_sound B J indices u v hp).2.2
  let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
  have hu : u ∉ rest := by simp [rest]
  have hv : v ∉ rest := by simp [rest]
  have hsu := clearPairColumns_other B u v u rest J hu
  have hsv := clearPairColumns_other B u v v rest J hv
  have hru := polarEliminate_other B fuel rest (clearPairColumns B u v rest J).1 u hu
  have hrv := polarEliminate_other B fuel rest (clearPairColumns B u v rest J).1 v hv
  simp only [polarEliminate, hp]
  change B (matrixColumn (polarEliminate B fuel rest (clearPairColumns B u v rest J).1).1 u)
    (matrixColumn (polarEliminate B fuel rest (clearPairColumns B u v rest J).1).1 v) = true
  rw [hru, hrv, hsu, hsv]
  exact huv
theorem polarEliminate_all_pairs {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) :
    ∀ p ∈ (polarEliminate B fuel indices J).2.2,
      B (matrixColumn (polarEliminate B fuel indices J).1 p.1)
        (matrixColumn (polarEliminate B fuel indices J).1 p.2) = true := by
  induction fuel generalizing indices J with
  | zero => simp [polarEliminate]
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have hf := polarEliminate_first_pair B fuel indices J u v hp
      have ht := ih rest next
      simp only [polarEliminate, hp]
      intro p hp'
      simp only [List.mem_cons] at hp'
      rcases hp' with he | hm
      · subst p
        simpa [polarEliminate, hp, rest, next] using hf
      · exact ht p hm

end SectorSimulation
#print axioms SectorSimulation.polarEliminate_other
#print axioms SectorSimulation.polarEliminate_first_pair
#print axioms SectorSimulation.polarEliminate_all_pairs
