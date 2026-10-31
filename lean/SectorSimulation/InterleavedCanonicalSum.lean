import SectorSimulation.InterleavedCharacter
import SectorSimulation.CanonicalCharacterDot
import SectorSimulation.CanonicalInterleavedLayout
import Mathlib.Tactic.SplitIfs

namespace SectorSimulation

/-- Canonical block positions select even, odd, then radical positions in an interleaved vector. -/
def interleavedIndexFromCanonical {k m : Nat} :
    Fin ((k + k) + m) → Fin ((k + k) + m) := fun i =>
  if hleft : i.val < k then ⟨2 * i.val, by have hi := i.isLt; omega⟩
  else if hright : i.val < k + k then ⟨2 * (i.val - k) + 1, by have hi := i.isLt; omega⟩
  else ⟨i.val, by have hi := i.isLt; omega⟩

/-- The inverse index permutation sends even/odd positions back to their canonical block. -/
def canonicalIndexFromInterleaved {k m : Nat} :
    Fin ((k + k) + m) → Fin ((k + k) + m) := fun i =>
  if hpaired : i.val < k + k then
    if heven : i.val % 2 = 0 then ⟨i.val / 2, by have hi := i.isLt; omega⟩
    else ⟨k + i.val / 2, by have hi := i.isLt; omega⟩
  else ⟨i.val, by have hi := i.isLt; omega⟩

theorem canonicalIndexFromInterleaved_leftInverse {k m : Nat} (i : Fin ((k + k) + m)) :
    canonicalIndexFromInterleaved (interleavedIndexFromCanonical i) = i := by
  apply Fin.ext
  by_cases hleft : i.val < k
  · have hpair : 2 * i.val < k + k := by omega
    have heven : (2 * i.val) % 2 = 0 := by omega
    simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hleft, hpair, heven]
  · by_cases hright : i.val < k + k
    · have hpair : 2 * (i.val - k) + 1 < k + k := by omega
      have hodd : (2 * (i.val - k) + 1) % 2 ≠ 0 := by omega
      simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hleft, hright,
        hpair] <;> omega
    · simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hleft, hright]

theorem interleavedIndexFromCanonical_leftInverse {k m : Nat} (i : Fin ((k + k) + m)) :
    interleavedIndexFromCanonical (canonicalIndexFromInterleaved i) = i := by
  apply Fin.ext
  by_cases hpair : i.val < k + k
  · by_cases heven : i.val % 2 = 0
    · have hleft : i.val / 2 < k := by omega
      have hpaired : 2 * (i.val / 2) < k + k := by omega
      simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hpair, heven,
        hleft] <;> omega
    · have hright : k ≤ k + i.val / 2 := by omega
      have hpaired : k + i.val / 2 < k + k := by omega
      have hnotleft : ¬ k + i.val / 2 < k := by omega
      simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hpair, heven,
        hpaired, hnotleft] <;> omega
  · have hnotleft : ¬ i.val < k := by omega
    simp [canonicalIndexFromInterleaved, interleavedIndexFromCanonical, hpair, hnotleft]

/-- Re-interleaving a canonical vector is the inverse index reindexing. -/
theorem interleavedVectorOfCanonical_coordinateReindex {k m : Nat}
    (x : BinaryVector ((k + k) + m)) :
    interleavedVectorOfCanonical x =
      coordinateReindex (@canonicalIndexFromInterleaved k m) x := by
  funext i
  by_cases hpair : i.val < 2 * k
  · have hpaired : i.val < k + k := by omega
    by_cases heven : i.val % 2 = 0
    · simp [interleavedVectorOfCanonical, canonicalIndexFromInterleaved, coordinateReindex,
        canonicalLeft, hpair, hpaired, heven]
    · have hodd : i.val % 2 = 1 := by omega
      have hdiv := Nat.mod_add_div i.val 2
      simp [interleavedVectorOfCanonical, canonicalIndexFromInterleaved, coordinateReindex,
        canonicalRight, hpair, hpaired, hodd]
      apply congrArg x
      apply Fin.ext
      change i.val / 2 + k = k + i.val / 2
      exact Nat.add_comm _ _
  · have hpaired : ¬ i.val < k + k := by omega
    have hidx : k + k + (i.val - 2 * k) = i.val := by omega
    simp [interleavedVectorOfCanonical, canonicalIndexFromInterleaved, coordinateReindex,
      canonicalRadical, hpair, hpaired, hidx]

/-- The canonical block map is the coordinate reindexing from the interleaved layout. -/
theorem canonicalBlockOfInterleaved_coordinateReindex {k m : Nat}
    (y : BinaryVector ((k + k) + m)) :
    canonicalBlockOfInterleaved y =
      coordinateReindex (@interleavedIndexFromCanonical k m) y := by
  let f := @canonicalIndexFromInterleaved k m
  let g := @interleavedIndexFromCanonical k m
  have hfg : ∀ i, f (g i) = i := canonicalIndexFromInterleaved_leftInverse
  have hRf : coordinateReindex f (canonicalBlockOfInterleaved y) = y := by
    simpa only [f, ← interleavedVectorOfCanonical_coordinateReindex] using
      (interleavedVectorOfCanonical_leftInverse y)
  have hcomp (x : BinaryVector ((k + k) + m)) :
      coordinateReindex g (coordinateReindex f x) = x := by
    funext i
    change x (f (g i)) = x i
    rw [hfg i]
  calc
    canonicalBlockOfInterleaved y =
        coordinateReindex g (coordinateReindex f (canonicalBlockOfInterleaved y)) :=
      (hcomp (canonicalBlockOfInterleaved y)).symm
    _ = coordinateReindex g y := congrArg (coordinateReindex g) hRf

/-- Pair and radical phases read directly from the interleaved even/odd coordinates. -/
def interleavedCanonicalCharacterWalshSum {k m : Nat}
    (ps qs : List (Bool × Bool)) (bs ds : List Bool) (c : Bool) : Int :=
  ((binaryBasis ((k + k) + m)).map (fun y => integerWalshSign
    (Bool.xor
      (pairPhaseEval ps
        (vectorPairAssignment
          (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩)
          (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩))
        (radicalPhaseEval bs
          (vectorAssignment (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩)) c))
      (canonicalLinearCharacter qs ds (canonicalBlockOfInterleaved y))))).sum

/-- The explicit interleaved pair-phase sum is a coordinate reindex of the canonical character sum. -/
theorem interleavedCanonicalCharacterWalshSum_eq {k m : Nat}
    (ps qs : List (Bool × Bool)) (bs ds : List Bool) (c : Bool) :
    interleavedCanonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c =
      canonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c := by
  unfold interleavedCanonicalCharacterWalshSum
  calc
    _ = ((binaryBasis ((k + k) + m)).map (fun y => integerWalshSign
        (Bool.xor
          (canonicalPhaseOnVector ps bs c (canonicalBlockOfInterleaved y))
          (canonicalLinearCharacter qs ds (canonicalBlockOfInterleaved y))))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro y hy
      rw [← canonicalBlockOfInterleaved_phase ps bs c y]
    _ = canonicalCharacterWalshSum ps qs bs ds c := by
      simpa only [canonicalCharacterWalshSum] using
        (canonicalBlockOfInterleaved_integerSum (k := k) (m := m)
          (fun x => integerWalshSign
            (Bool.xor (canonicalPhaseOnVector ps bs c x)
              (canonicalLinearCharacter qs ds x))))

/-- Closed form for an interleaved pair-phase sum with its transported canonical character. -/
theorem interleavedCanonicalCharacterWalshSum_closed {k m : Nat}
    (ps qs : List (Bool × Bool)) (bs ds : List Bool) (c : Bool)
    (hp : ps.length = k) (hq : qs.length = k) (hb : bs.length = m) (hd : ds.length = m) :
    interleavedCanonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c =
      if (radicalCoefficientsXor bs ds).any id then 0 else (2 : Int)^(m+k) *
        integerWalshSign (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps qs))) := by
  rw [interleavedCanonicalCharacterWalshSum_eq, canonicalCharacterWalshSum_closed
    ps qs bs ds c hp hq hb hd]

/-- The generated interleaved phase paired with an arbitrary wire character. -/
def interleavedWireCharacterWalshSum {k m : Nat}
    (ps : List (Bool × Bool)) (bs : List Bool) (c : Bool)
    (l : BinaryVector ((k + k) + m)) : Int :=
  ((binaryBasis ((k + k) + m)).map (fun y => integerWalshSign
    (Bool.xor
      (pairPhaseEval ps
        (vectorPairAssignment
          (fun i : Fin k => y ⟨2 * i.val, by have hi := i.isLt; omega⟩)
          (fun i : Fin k => y ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩))
        (radicalPhaseEval bs
          (vectorAssignment (fun i : Fin m => y ⟨2 * k + i.val, by have hi := i.isLt; omega⟩)) c))
      (walshWireParity (List.finRange ((k + k) + m)) l y)))).sum

/-- Any interleaved wire character becomes canonical pair/radical coefficients after layout reindexing. -/
theorem interleavedWireCharacterWalshSum_eq {k m : Nat}
    (ps : List (Bool × Bool)) (bs : List Bool) (c : Bool)
    (l : BinaryVector ((k + k) + m)) :
    interleavedWireCharacterWalshSum (k := k) (m := m) ps bs c l =
      interleavedCanonicalCharacterWalshSum (k := k) (m := m) ps
        (vectorPairAssignment
          (canonicalLeft (coordinateReindex (@interleavedIndexFromCanonical k m) l))
          (canonicalRight (coordinateReindex (@interleavedIndexFromCanonical k m) l)))
        bs
        (vectorAssignment (canonicalRadical (coordinateReindex (@interleavedIndexFromCanonical k m) l))) c := by
  let g := @interleavedIndexFromCanonical k m
  let f := @canonicalIndexFromInterleaved k m
  let canonical := coordinateReindex g l
  have hfg : ∀ i, f (g i) = i := canonicalIndexFromInterleaved_leftInverse
  have hgf : ∀ i, g (f i) = i := interleavedIndexFromCanonical_leftInverse
  have hcharacter (y : BinaryVector ((k + k) + m)) :
      canonicalLinearCharacter
          (vectorPairAssignment (canonicalLeft canonical) (canonicalRight canonical))
          (vectorAssignment (canonicalRadical canonical)) (canonicalBlockOfInterleaved y) =
        walshWireParity (List.finRange ((k + k) + m)) l y := by
    rw [canonicalLinearCharacter_dot canonical (canonicalBlockOfInterleaved y)]
    rw [canonicalBlockOfInterleaved_coordinateReindex]
    rw [walshWireParity_coordinateReindex f g hfg hgf canonical y]
    have hcanonical : coordinateReindex f canonical = l := by
      funext i
      change l (g (f i)) = l i
      rw [hgf i]
    rw [hcanonical]
  unfold interleavedWireCharacterWalshSum interleavedCanonicalCharacterWalshSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  apply congrArg integerWalshSign
  rw [hcharacter y]

/-- Closed form for the generated interleaved phase with any wire character. -/
theorem interleavedWireCharacterWalshSum_closed {k m : Nat}
    (ps : List (Bool × Bool)) (bs : List Bool) (c : Bool)
    (l : BinaryVector ((k + k) + m)) (hp : ps.length = k) (hb : bs.length = m) :
    let canonical := coordinateReindex (@interleavedIndexFromCanonical k m) l
    let qs := vectorPairAssignment (canonicalLeft canonical) (canonicalRight canonical)
    let ds := vectorAssignment (canonicalRadical canonical)
    interleavedWireCharacterWalshSum (k := k) (m := m) ps bs c l =
      if (radicalCoefficientsXor bs ds).any id then 0
      else (2 : Int)^(m+k) * integerWalshSign
        (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps qs))) := by
  let canonical := coordinateReindex (@interleavedIndexFromCanonical k m) l
  let qs := vectorPairAssignment (canonicalLeft canonical) (canonicalRight canonical)
  let ds := vectorAssignment (canonicalRadical canonical)
  change interleavedWireCharacterWalshSum (k := k) (m := m) ps bs c l =
    if (radicalCoefficientsXor bs ds).any id then 0
    else (2 : Int)^(m+k) * integerWalshSign
      (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps qs)))
  rw [interleavedWireCharacterWalshSum_eq]
  exact interleavedCanonicalCharacterWalshSum_closed ps qs bs ds c hp
    (vectorPairAssignment_length _ _) hb (vectorAssignment_length _)

/-- A recorded coordinate order consists of two entries per pair followed by its residual coordinates. -/
theorem recordedCoordinateOrder_dimension {n : Nat}
    (pairs : List (Fin n × Fin n)) (hlen : (recordedCoordinateOrder pairs).length = n) :
    ∃ m, pairs.length + pairs.length + m = n := by
  refine ⟨(unpairedIndices (List.finRange n) pairs).length, ?_⟩
  have h := hlen
  unfold recordedCoordinateOrder at h
  rw [List.length_append, pairEndpoints_length] at h
  omega

theorem recordedCoordinateOrder_dimension_exists {n : Nat}
    (pairs : List (Fin n × Fin n)) (hlen : (recordedCoordinateOrder pairs).length = n) :
    ∃ k m, pairs.length = k ∧ n = k + k + m := by
  obtain ⟨m, hdim⟩ := recordedCoordinateOrder_dimension pairs hlen
  exact ⟨pairs.length, m, rfl, by omega⟩

/-- Reindexing both arguments of the Walsh dot product by a permutation preserves it. -/
theorem walshWireParity_coordinateReindex_both {n : Nat}
    (f g : Fin n → Fin n) (hfg : ∀ i, f (g i) = i) (hgf : ∀ i, g (f i) = i)
    (u v : BinaryVector n) :
    walshWireParity (List.finRange n) (coordinateReindex g u) (coordinateReindex g v) =
      walshWireParity (List.finRange n) u v := by
  rw [walshWireParity_coordinateReindex f g hfg hgf (coordinateReindex g u) v]
  have hu : coordinateReindex f (coordinateReindex g u) = u := by
    funext i
    exact congrArg u (hgf i)
  rw [hu]

end SectorSimulation
