import SectorSimulation.PairEndpointIndex
namespace SectorSimulation

theorem recordedCoordinateAt_pair_first {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (i : Nat) (hi : i < pairs.length) :
    recordedCoordinateAt pairs hlen ⟨2*i, by
      have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
        unfold recordedCoordinateOrder; rw [List.length_append, pairEndpoints_length]; omega
      omega⟩ = pairs[i].1 := by
  unfold recordedCoordinateAt recordedCoordinateOrder
  change (pairs.flatMap (fun p => [p.1,p.2]) ++ unpairedIndices (List.finRange n) pairs)[2*i]'_ = pairs[i].1
  rw [List.getElem_append_left]
  exact pairEndpoints_get_first pairs i hi

theorem recordedCoordinateAt_pair_second {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (i : Nat) (hi : i < pairs.length) :
    recordedCoordinateAt pairs hlen ⟨2*i+1, by
      have h : 2 * pairs.length ≤ (recordedCoordinateOrder pairs).length := by
        unfold recordedCoordinateOrder; rw [List.length_append, pairEndpoints_length]; omega
      omega⟩ = pairs[i].2 := by
  unfold recordedCoordinateAt recordedCoordinateOrder
  change (pairs.flatMap (fun p => [p.1,p.2]) ++ unpairedIndices (List.finRange n) pairs)[2*i+1]'_ = pairs[i].2
  rw [List.getElem_append_left]
  exact pairEndpoints_get_second pairs i hi



end SectorSimulation