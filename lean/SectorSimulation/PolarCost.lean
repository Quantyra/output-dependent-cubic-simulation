import SectorSimulation.PolarNormalCertificate
namespace SectorSimulation

theorem pairColumnOps_length_le {n : Nat} (B : BinaryVector n -> BinaryVector n -> Bool)
    (J : BinaryMatrix n) (t u v : Fin n) : (pairColumnOps B J t u v).length <= 2 := by
  cases h1 : B (matrixColumn J t) (matrixColumn J v) <;>
    cases h2 : B (matrixColumn J t) (matrixColumn J u) <;>
    simp [pairColumnOps, h1, h2]

theorem clearPairColumns_length_le {n : Nat} (B : BinaryVector n -> BinaryVector n -> Bool)
    (u v : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n) :
    (clearPairColumns B u v ts J).2.length <= 2 * ts.length := by
  induction ts generalizing J with
  | nil => simp [clearPairColumns]
  | cons t ts ih =>
    simp only [clearPairColumns, List.length_append, List.length_cons]
    have h := pairColumnOps_length_le B J t u v
    have ht := ih (clearPairColumn B J t u v)
    omega

theorem polarEliminate_program_length_le {n : Nat} (B : BinaryVector n -> BinaryVector n -> Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n) :
    (polarEliminate B fuel indices J).2.1.length <= 2 * fuel * indices.length := by
  induction fuel generalizing indices J with
  | zero => simp [polarEliminate]
  | succ fuel ih =>
    cases hp : findPolarPair B J indices with
    | none => simp [polarEliminate, hp]
    | some pair =>
      rcases pair with ⟨u,v⟩
      let rest := indices.filter (fun i => decide (i ≠ u) && decide (i ≠ v))
      let next := (clearPairColumns B u v rest J).1
      have hlen : rest.length <= indices.length := List.length_filter_le _ _
      have hs := clearPairColumns_length_le B u v rest J
      have ht := ih rest next
      simp only [polarEliminate, hp, List.length_append]
      have hm : 2 * fuel * rest.length <= 2 * fuel * indices.length := Nat.mul_le_mul_left (2 * fuel) hlen
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add] at *
      dsimp [rest, next] at hlen hs ht hm
      simp only [ne_eq] at *
      omega
end SectorSimulation
