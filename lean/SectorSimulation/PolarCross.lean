import SectorSimulation.PolarSelected
namespace SectorSimulation

theorem polarEliminate_preserves_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) (j : Fin n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (hn : indices.Nodup) (hj : j ∉ indices)
    (horth : ∀ t ∈ indices, B (matrixColumn J t) (matrixColumn J j) = false) :
    ∀ t ∈ indices, B (matrixColumn (polarEliminate B fuel indices J).1 t)
      (matrixColumn J j) = false := by
  induction fuel generalizing indices J with
  | zero => exact horth
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simpa [polarEliminate, hp] using horth
    | some pair =>
      rcases pair with ⟨u,v⟩
      obtain ⟨hui,hvi,_⟩ := findPolarPair_sound B J indices u v hp
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have hu : u ∉ rest := by simp [rest]
      have hv : v ∉ rest := by simp [rest]
      have hjr : j ∉ rest := by simp [rest, hj]
      have hnr : rest.Nodup := List.Nodup.sublist List.filter_sublist hn
      have hjnext : matrixColumn next j = matrixColumn J j := clearPairColumns_other B u v j rest J hjr
      have hstep := clearPairColumns_preserves_prior B u v j rest J hadd hzero hu hv hjr hnr (horth u hui) (horth v hvi)
      have hrest : ∀ t ∈ rest, B (matrixColumn next t) (matrixColumn next j) = false := by
        intro t ht
        rw [hjnext, hstep t ht]
        exact horth t ((List.mem_filter.mp ht).1)
      have hrec := ih rest next hnr hjr hrest
      simp only [polarEliminate, hp]
      intro t ht
      by_cases htr : t ∈ rest
      · change B (matrixColumn (polarEliminate B fuel rest next).1 t) (matrixColumn J j) = false
        have hx := hrec t htr
        rw [hjnext] at hx
        exact hx
      · have hrt := polarEliminate_other B fuel rest next t htr
        have hts := clearPairColumns_other B u v t rest J htr
        change B (matrixColumn (polarEliminate B fuel rest next).1 t) (matrixColumn J j) = false
        rw [hrt, hts]
        exact horth t ht
end SectorSimulation
