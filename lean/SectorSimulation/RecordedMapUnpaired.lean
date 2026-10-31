import SectorSimulation.RecordedMapEndpoints
namespace SectorSimulation

theorem recordedCoordinateAt_unpaired {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (i : Nat) (hi : i < (unpairedIndices (List.finRange n) pairs).length) :
    recordedCoordinateAt pairs hlen ⟨2*pairs.length+i, by
      have h : (recordedCoordinateOrder pairs).length = 2*pairs.length + (unpairedIndices (List.finRange n) pairs).length := by
        unfold recordedCoordinateOrder; rw [List.length_append, pairEndpoints_length]
      omega⟩ = (unpairedIndices (List.finRange n) pairs)[i] := by
  unfold recordedCoordinateAt recordedCoordinateOrder
  change (pairs.flatMap (fun p => [p.1,p.2]) ++ unpairedIndices (List.finRange n) pairs)[2*pairs.length+i]'_ = _
  rw [List.getElem_append_right (by rw [pairEndpoints_length]; omega)]
  simp only [pairEndpoints_length, Nat.add_sub_cancel_left]


end SectorSimulation