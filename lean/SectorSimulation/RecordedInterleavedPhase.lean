import SectorSimulation.RecordedAssignment
import SectorSimulation.CanonicalInterleavedLayout

namespace SectorSimulation

/-- The phase of the recorded disjoint pairs, read through the inverse coordinate
map, is exactly the pair phase on their even/odd interleaved coordinates. -/
theorem recordedPairPhase_interleaved {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hinj : Function.Injective (recordedCoordinateAt pairs hlen))
    (hsurj : ∀ x, ∃ i, recordedCoordinateAt pairs hlen i = x)
    (y : BinaryVector n) (c : Bool) :
    Bool.xor c (evalPhase (recordedPairPhase pairs)
      (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y)) =
    pairPhaseEval (List.replicate pairs.length (false, false))
      (vectorPairAssignment
        (fun j : Fin pairs.length => y ⟨2 * j.val, by
          have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
            unfold recordedCoordinateOrder
            rw [List.length_append, pairEndpoints_length]
            omega
          omega⟩)
        (fun j : Fin pairs.length => y ⟨2 * j.val + 1, by
          have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
            unfold recordedCoordinateOrder
            rw [List.length_append, pairEndpoints_length]
            omega
          omega⟩)) c := by
  calc
    _ = pairPhaseEval (List.replicate pairs.length (false, false))
        (pairs.map (fun q =>
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y q.1,
           coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y q.2))) c :=
      (recordedPairPhase_pairEval pairs
        (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y) c).symm
    _ = pairPhaseEval (List.replicate pairs.length (false, false))
        (vectorPairAssignment
          (fun j : Fin pairs.length => y ⟨2 * j.val, by
            have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
              unfold recordedCoordinateOrder
              rw [List.length_append, pairEndpoints_length]
              omega
            omega⟩)
          (fun j : Fin pairs.length => y ⟨2 * j.val + 1, by
            have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
              unfold recordedCoordinateOrder
              rw [List.length_append, pairEndpoints_length]
              omega
            omega⟩)) c := by
      rw [recordedPair_assignment_reindexed pairs hlen hinj hsurj y]

end SectorSimulation
