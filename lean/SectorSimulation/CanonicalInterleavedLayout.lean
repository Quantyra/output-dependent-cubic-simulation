import SectorSimulation.CanonicalVectorWalsh

namespace SectorSimulation

/-- Read interleaved left/right coordinates and trailing radical coordinates as canonical blocks. -/
def canonicalBlockOfInterleaved {k m : Nat}
    (y : BinaryVector ((k+k)+m)) : BinaryVector ((k+k)+m) :=
  canonicalJoin
    (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩)
    (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
    (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩)

theorem canonicalBlockOfInterleaved_left {k m : Nat}
    (y : BinaryVector ((k+k)+m)) :
    canonicalLeft (canonicalBlockOfInterleaved y) =
      (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩) := by
  exact canonicalLeft_join _ _ _

theorem canonicalBlockOfInterleaved_right {k m : Nat}
    (y : BinaryVector ((k+k)+m)) :
    canonicalRight (canonicalBlockOfInterleaved y) =
      (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) := by
  exact canonicalRight_join _ _ _

theorem canonicalBlockOfInterleaved_radical {k m : Nat}
    (y : BinaryVector ((k+k)+m)) :
    canonicalRadical (canonicalBlockOfInterleaved y) =
      (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩) := by
  exact canonicalRadical_join _ _ _

theorem canonicalBlockOfInterleaved_assignment {k m : Nat}
    (y : BinaryVector ((k+k)+m)) :
    canonicalAssignment (canonicalBlockOfInterleaved y) =
      (vectorAssignment (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩),
       vectorPairAssignment
         (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩)
         (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) := by
  unfold canonicalBlockOfInterleaved
  exact canonicalAssignment_join _ _ _

theorem canonicalBlockOfInterleaved_phase {k m : Nat}
    (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool)
    (y : BinaryVector ((k+k)+m)) :
    canonicalPhaseOnVector pairs radicals c (canonicalBlockOfInterleaved y) =
      pairPhaseEval pairs
        (vectorPairAssignment
          (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩)
          (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩))
        (radicalPhaseEval radicals
          (vectorAssignment (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩)) c) := by
  unfold canonicalBlockOfInterleaved
  exact canonicalPhaseOnVector_join _ _ _ _ _ _

end SectorSimulation
