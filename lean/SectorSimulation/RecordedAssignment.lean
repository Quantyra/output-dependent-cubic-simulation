import SectorSimulation.RecordedPhaseEval
namespace SectorSimulation

theorem recordedPair_assignment_reindexed {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hinj : Function.Injective (recordedCoordinateAt pairs hlen))
    (hsurj : ∀ x, ∃ i, recordedCoordinateAt pairs hlen i = x)
    (y : BinaryVector n) :
    pairs.map (fun q => (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y q.1,
      coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y q.2)) =
    vectorPairAssignment
      (fun j : Fin pairs.length => y ⟨2*j.val, by
        have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
          unfold recordedCoordinateOrder; rw [List.length_append, pairEndpoints_length]; omega
        omega⟩)
      (fun j : Fin pairs.length => y ⟨2*j.val+1, by
        have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
          unfold recordedCoordinateOrder; rw [List.length_append, pairEndpoints_length]; omega
        omega⟩) := by
  apply List.ext_getElem
  · simp [vectorPairAssignment]
  · intro i hi1 hi2
    have hi : i < pairs.length := by simpa using hi1
    simp only [List.getElem_map, vectorPairAssignment, List.getElem_finRange, Fin.val_cast] at *
    apply Prod.ext
    · rw [← recordedCoordinateAt_pair_first pairs hlen i hi]
      exact coordinateReindex_inverse_at _ hinj hsurj y _
    · rw [← recordedCoordinateAt_pair_second pairs hlen i hi]
      exact coordinateReindex_inverse_at _ hinj hsurj y _


end SectorSimulation