import SectorSimulation.PolarCost
import SectorSimulation.QuadraticSourcePolar
namespace SectorSimulation

theorem sourceQuadratic_normal_certificate {n : Nat} (src : PhaseANF n)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hdegree : phaseWithinDegree 2 src = true)
    (hn : indices.Nodup) (hbound : indices.length <= fuel) :
    let result := polarEliminate (phasePolar src) fuel indices J
    runColumnAdds result.2.1 J = result.1 ∧
    runColumnAdds result.2.1.reverse result.1 = J ∧
    (∀ p ∈ result.2.2, p.1 ∈ indices ∧ p.2 ∈ indices) ∧
    (∀ p ∈ result.2.2, p.1 ≠ p.2) ∧
    result.2.2.Pairwise pairDisjoint ∧
    (∀ p ∈ result.2.2, (phasePolar src) (matrixColumn result.1 p.1) (matrixColumn result.1 p.2) = true) ∧
    result.2.2.Pairwise (pairOrthogonal (phasePolar src) result.1) ∧
    (∀ u ∈ unpairedIndices indices result.2.2, ∀ v ∈ unpairedIndices indices result.2.2,
      (phasePolar src) (matrixColumn result.1 u) (matrixColumn result.1 v) = false) ∧
    (∀ t ∈ unpairedIndices indices result.2.2, ∀ p ∈ result.2.2,
      (phasePolar src) (matrixColumn result.1 t) (matrixColumn result.1 p.1) = false ∧
      (phasePolar src) (matrixColumn result.1 t) (matrixColumn result.1 p.2) = false) := by
  obtain ⟨ts, hts, heval, hpolar, halt, hadd, hright⟩ := sourceQuadratic_hasPolar src hdegree
  have ha : ∀ a b z, phasePolar src (binaryShift a b) z = Bool.xor (phasePolar src a z) (phasePolar src b z) := by
    intro a b z; simp only [hpolar, hadd]
  have hz : ∀ z, phasePolar src (fun _ => false) z = false := by
    intro z
    rw [hpolar]
    clear hts heval hpolar halt hadd hright
    induction ts with
    | nil => rfl
    | cons t ts ih => cases t <;> simp [termsPolar, termPolar, ih]
  have hl : ∀ x, phasePolar src x x = false := by
    intro x; rw [hpolar]; exact halt x
  have hs : ∀ x y, phasePolar src x y = phasePolar src y x := by
    intro x y; simp only [hpolar, termsPolar_symmetric]
  exact polarEliminate_normal_certificate (phasePolar src) fuel indices J ha hz hl hs hn hbound
end SectorSimulation
