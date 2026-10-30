import SectorSimulation.PolarCross
namespace SectorSimulation

theorem polarEliminate_first_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) (u v : Fin n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (halt : ∀ x, B x x = false) (hsym : ∀ x y, B x y = B y x)
    (hn : indices.Nodup) (hp : findPolarPair B J indices = some (u,v)) :
    ∀ t ∈ indices, t ≠ u → t ≠ v →
      B (matrixColumn (polarEliminate B (fuel+1) indices J).1 t)
        (matrixColumn (polarEliminate B (fuel+1) indices J).1 u) = false ∧
      B (matrixColumn (polarEliminate B (fuel+1) indices J).1 t)
        (matrixColumn (polarEliminate B (fuel+1) indices J).1 v) = false := by
  have huv := (findPolarPair_sound B J indices u v hp).2.2
  have hvu : B (matrixColumn J v) (matrixColumn J u) = true := by rw [hsym, huv]
  let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
  let next := (clearPairColumns B u v rest J).1
  have hu : u ∉ rest := by simp [rest]
  have hv : v ∉ rest := by simp [rest]
  have hnr : rest.Nodup := List.Nodup.sublist List.filter_sublist hn
  have huJ : matrixColumn next u = matrixColumn J u := clearPairColumns_other B u v u rest J hu
  have hvJ : matrixColumn next v = matrixColumn J v := clearPairColumns_other B u v v rest J hv
  have hclear := clearPairColumns_orthogonal B u v rest J hadd hzero (halt _) (halt _) huv hvu hu hv hnr
  have hou : ∀ t ∈ rest, B (matrixColumn next t) (matrixColumn next u) = false := by
    intro t ht
    rw [huJ]
    exact (hclear t ht).1
  have hov : ∀ t ∈ rest, B (matrixColumn next t) (matrixColumn next v) = false := by
    intro t ht
    rw [hvJ]
    exact (hclear t ht).2
  have hrecU := polarEliminate_preserves_orthogonal B fuel rest next u hadd hzero hnr hu hou
  have hrecV := polarEliminate_preserves_orthogonal B fuel rest next v hadd hzero hnr hv hov
  have hkeepU := polarEliminate_other B fuel rest next u hu
  have hkeepV := polarEliminate_other B fuel rest next v hv
  simp only [polarEliminate, hp]
  intro t ht htu htv
  have htr : t ∈ rest := by simp [rest, ht, htu, htv]
  change B (matrixColumn (polarEliminate B fuel rest next).1 t)
      (matrixColumn (polarEliminate B fuel rest next).1 u) = false ∧
    B (matrixColumn (polarEliminate B fuel rest next).1 t)
      (matrixColumn (polarEliminate B fuel rest next).1 v) = false
  rw [hkeepU, hkeepV]
  exact ⟨hrecU t htr, hrecV t htr⟩
end SectorSimulation
