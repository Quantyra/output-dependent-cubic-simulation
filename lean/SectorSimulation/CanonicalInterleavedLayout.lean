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

/-- Interleave the left/right blocks again and retain the trailing radical block. -/
def interleavedVectorOfCanonical {k m : Nat}
    (x : BinaryVector ((k+k)+m)) : BinaryVector ((k+k)+m) :=
  fun i =>
    if h : i.val < 2*k then
      if i.val % 2 = 0 then
        canonicalLeft x ⟨i.val / 2, by have hi := i.isLt; omega⟩
      else
        canonicalRight x ⟨i.val / 2, by have hi := i.isLt; omega⟩
    else
      canonicalRadical x ⟨i.val - 2*k, by have hi := i.isLt; omega⟩

theorem interleavedVectorOfCanonical_leftInverse {k m : Nat}
    (y : BinaryVector ((k+k)+m)) :
    interleavedVectorOfCanonical (canonicalBlockOfInterleaved y) = y := by
  funext i
  dsimp [interleavedVectorOfCanonical]
  by_cases h : i.val < 2*k
  · simp only [dif_pos h]
    by_cases heven : i.val % 2 = 0
    · simp only [if_pos heven]
      rw [canonicalBlockOfInterleaved_left]
      change y ⟨2 * (i.val / 2), by omega⟩ = y i
      apply congrArg y
      apply Fin.ext
      change 2 * (i.val / 2) = i.val
      have hmod := Nat.mod_add_div i.val 2
      omega
    · simp only [if_neg heven]
      rw [canonicalBlockOfInterleaved_right]
      change y ⟨2 * (i.val / 2) + 1, by omega⟩ = y i
      apply congrArg y
      apply Fin.ext
      change 2 * (i.val / 2) + 1 = i.val
      have hmod := Nat.mod_add_div i.val 2
      omega
  · simp only [dif_neg h]
    rw [canonicalBlockOfInterleaved_radical]
    change y ⟨2 * k + (i.val - 2 * k), by omega⟩ = y i
    apply congrArg y
    apply Fin.ext
    change 2 * k + (i.val - 2 * k) = i.val
    omega

theorem canonicalBlockOfInterleaved_injective {k m : Nat} :
    Function.Injective (@canonicalBlockOfInterleaved k m) := by
  intro y z h
  calc
    y = interleavedVectorOfCanonical (canonicalBlockOfInterleaved y) :=
      (interleavedVectorOfCanonical_leftInverse y).symm
    _ = interleavedVectorOfCanonical (canonicalBlockOfInterleaved z) := congrArg _ h
    _ = z := interleavedVectorOfCanonical_leftInverse z

theorem canonicalBlockOfInterleaved_rightInverse {k m : Nat}
    (x : BinaryVector ((k+k)+m)) :
    canonicalBlockOfInterleaved (interleavedVectorOfCanonical x) = x := by
  have hleft :
      canonicalLeft (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x)) =
        canonicalLeft x := by
    rw [canonicalBlockOfInterleaved_left]
    funext i
    have hlt : 2 * i.val < 2 * k := by have hi := i.isLt; omega
    have hmod : (2 * i.val) % 2 = 0 := by omega
    have hdiv : (2 * i.val) / 2 = i.val := by omega
    simp [interleavedVectorOfCanonical, hlt, hmod, hdiv]
  have hright :
      canonicalRight (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x)) =
        canonicalRight x := by
    rw [canonicalBlockOfInterleaved_right]
    funext i
    have hlt : 2 * i.val + 1 < 2 * k := by have hi := i.isLt; omega
    have hmod : (2 * i.val + 1) % 2 = 1 := by omega
    have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
    simp [interleavedVectorOfCanonical, hlt, hmod, hdiv]
  have hradical :
      canonicalRadical (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x)) =
        canonicalRadical x := by
    rw [canonicalBlockOfInterleaved_radical]
    funext i
    have hnot : ¬ 2 * k + i.val < 2 * k := by omega
    have hsub : 2 * k + i.val - 2 * k = i.val := by omega
    simp [interleavedVectorOfCanonical, hnot, hsub]
  calc
    canonicalBlockOfInterleaved (interleavedVectorOfCanonical x) =
        canonicalJoin
          (canonicalLeft (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x)))
          (canonicalRight (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x)))
          (canonicalRadical (canonicalBlockOfInterleaved (interleavedVectorOfCanonical x))) :=
      (canonicalJoin_split _).symm
    _ = canonicalJoin (canonicalLeft x) (canonicalRight x) (canonicalRadical x) := by
      rw [hleft, hright, hradical]
    _ = x := canonicalJoin_split x

theorem canonicalBlockOfInterleaved_surjective {k m : Nat} :
    Function.Surjective (@canonicalBlockOfInterleaved k m) := by
  intro x
  exact ⟨interleavedVectorOfCanonical x, canonicalBlockOfInterleaved_rightInverse x⟩

theorem canonicalBlockOfInterleaved_basis_perm (k m : Nat) :
    ((binaryBasis ((k+k)+m)).map (@canonicalBlockOfInterleaved k m)).Perm
      (binaryBasis ((k+k)+m)) := by
  have hnd : ((binaryBasis ((k+k)+m)).map (@canonicalBlockOfInterleaved k m)).Nodup :=
    List.Pairwise.map _ (fun _ _ h he => h (canonicalBlockOfInterleaved_injective he))
      (binaryBasis_nodup _)
  have hm : ∀ z, z ∈ ((binaryBasis ((k+k)+m)).map (@canonicalBlockOfInterleaved k m)) ↔
      z ∈ binaryBasis ((k+k)+m) := by
    intro z
    constructor
    · intro hz
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
      exact binaryBasis_complete _
    · intro hz
      obtain ⟨y, hy⟩ := canonicalBlockOfInterleaved_surjective z
      apply List.mem_map.mpr
      exact ⟨y, binaryBasis_complete y, hy⟩
  apply List.perm_iff_count.mpr
  intro z
  rw [hnd.count, (binaryBasis_nodup ((k+k)+m)).count]
  simp [hm z]

theorem canonicalBlockOfInterleaved_integerSum {k m : Nat}
    (f : BinaryVector ((k+k)+m) → Int) :
    ((binaryBasis ((k+k)+m)).map (fun y => f (canonicalBlockOfInterleaved y))).sum =
      ((binaryBasis ((k+k)+m)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using
    integerSum_perm _ _ (canonicalBlockOfInterleaved_basis_perm k m) f

end SectorSimulation
