import SectorSimulation.InterleavedCharacter
import SectorSimulation.CanonicalCharacterDot
import SectorSimulation.CanonicalInterleavedLayout
import Mathlib.Tactic.SplitIfs
import SectorSimulation.ColumnAction
import SectorSimulation.HadamardMatrixSum
import SectorSimulation.PolarBasis
import SectorSimulation.PolarDisjoint
import SectorSimulation.QuadraticSourcePolar
import Mathlib.Logic.Equiv.Basic

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

/-- Transport a binary vector across an equality of coordinate dimensions. -/
def binaryVectorCast {n d : Nat} (h : n = d) (x : BinaryVector n) : BinaryVector d :=
  fun i => x (Fin.cast h.symm i)

theorem binaryVectorCast_refl {n : Nat} (x : BinaryVector n) :
    binaryVectorCast rfl x = x := by
  funext i
  change x (Fin.cast rfl i) = x i
  apply congrArg x
  apply Fin.ext
  rfl

def binaryVectorCastEquiv {n d : Nat} (h : n = d) : Equiv (BinaryVector n) (BinaryVector d) where
  toFun := binaryVectorCast h
  invFun := binaryVectorCast h.symm
  left_inv := by
    intro x
    cases h
    rw [binaryVectorCast_refl, binaryVectorCast_refl]
  right_inv := by
    intro x
    cases h
    rw [binaryVectorCast_refl, binaryVectorCast_refl]

theorem binaryVectorCast_basis_perm {n d : Nat} (h : n = d) :
    ((binaryBasis n).map (binaryVectorCast h)).Perm (binaryBasis d) := by
  have hinj : Function.Injective (binaryVectorCast h) := (binaryVectorCastEquiv h).injective
  have hnodup : ((binaryBasis n).map (binaryVectorCast h)).Nodup :=
    List.Pairwise.map _ (fun _ _ e he => e (hinj he)) (binaryBasis_nodup n)
  apply List.perm_iff_count.mpr
  intro y
  rw [hnodup.count, (binaryBasis_nodup d).count]
  have hmem : y ∈ (binaryBasis n).map (binaryVectorCast h) := by
    obtain ⟨x, hx⟩ := (binaryVectorCastEquiv h).surjective y
    exact List.mem_map.mpr ⟨x, binaryBasis_complete x, hx⟩
  simp [hmem, binaryBasis_complete]

theorem integerSum_binaryVectorCast {n d : Nat} (h : n = d)
    (g : BinaryVector d → Int) :
    ((binaryBasis n).map (fun x => g (binaryVectorCast h x))).sum =
      ((binaryBasis d).map g).sum := by
  simpa [List.map_map, Function.comp_def] using
    (integerSum_perm _ _ (binaryVectorCast_basis_perm h) g)

theorem walshWireParity_binaryVectorCast {n d : Nat} (h : n = d)
    (u v : BinaryVector n) :
    walshWireParity (List.finRange n) u v =
      walshWireParity (List.finRange d) (binaryVectorCast h u) (binaryVectorCast h v) := by
  cases h
  rfl

theorem interleavedPairAssignment_binaryVectorCast {n d k : Nat} (h : n = d)
    (hn : 2 * k ≤ n) (hd : 2 * k ≤ d) (y : BinaryVector n) :
    vectorPairAssignment
      (fun j : Fin k => y ⟨2 * j.val, by have hj := j.isLt; omega⟩)
      (fun j : Fin k => y ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩) =
    vectorPairAssignment
      (fun j : Fin k => binaryVectorCast h y ⟨2 * j.val, by have hj := j.isLt; omega⟩)
      (fun j : Fin k => binaryVectorCast h y ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩) := by
  cases h
  rfl

theorem radicalPhaseEval_replicate_false {m : Nat} (xs : List Bool) (c : Bool) :
    radicalPhaseEval (List.replicate m false) xs c = c := by
  induction m generalizing xs c with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ]
      cases xs with
      | nil => rfl
      | cons x xs =>
          change radicalPhaseEval (List.replicate m false) xs
            (Bool.xor c (false && x)) = c
          simpa using ih xs (Bool.xor c (false && x))

theorem radicalCoefficientsXor_replicate_false {m : Nat} (ds : List Bool)
    (hds : ds.length = m) :
    radicalCoefficientsXor (List.replicate m false) ds = ds := by
  induction m generalizing ds with
  | zero => cases ds with
    | nil => rfl
    | cons d ds => simp at hds
  | succ m ih =>
    cases ds with
    | nil => simp at hds
    | cons d ds =>
      have htail : ds.length = m := by simp at hds; omega
      simp only [List.replicate_succ, radicalCoefficientsXor]
      rw [ih ds htail]
      simp

theorem vectorAssignment_any_id_iff {n : Nat} (x : BinaryVector n) :
    (vectorAssignment x).any id = true ↔ ∃ i : Fin n, x i = true := by
  simp [vectorAssignment, List.any_eq_true]

theorem radicalCoefficientsXor_replicate_false_any {m : Nat} (x : BinaryVector m) :
    (radicalCoefficientsXor (List.replicate m false) (vectorAssignment x)).any id = true ↔
      ∃ i : Fin m, x i = true := by
  rw [radicalCoefficientsXor_replicate_false (vectorAssignment x)
    (vectorAssignment_length x)]
  exact vectorAssignment_any_id_iff x

theorem integerWalshSign_naturalAbs (b : Bool) :
    (integerWalshSign b).natAbs = 1 := by
  cases b <;> rfl

/-- Evaluate the source Walsh sum after transporting its recorded coordinates into the
canonical interleaved dimension. This is still a helper result, not a paper theorem. -/
theorem sourceWalshSum_recorded_interleaved_cast_closed {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    ∃ hlen : (recordedCoordinateOrder pairs).length = n,
      ∃ m, ∃ hsize : n = (pairs.length + pairs.length) + m,
        let f := recordedCoordinateAt pairs hlen
        let r := fun x => evalPhase (recordedPairPhase pairs) x
        let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
        let a := fun i => normalizedDifference
          (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
        let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
        let q := binaryVectorCast hsize (coordinateReindex f t)
        let canonical := coordinateReindex
          (@interleavedIndexFromCanonical pairs.length m) q
        let qs := vectorPairAssignment (canonicalLeft canonical) (canonicalRight canonical)
        let ds := vectorAssignment (canonicalRadical canonical)
        sourceWalshSum p l =
          if (radicalCoefficientsXor (List.replicate m false) ds).any id then 0
          else (2 : Int)^(m + pairs.length) * integerWalshSign
            (Bool.xor c (hyperbolicSignature
              (pairCoefficientsXor (List.replicate pairs.length (false, false)) qs))) := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  dsimp only [out, pairs]
  obtain ⟨hlen, hsum⟩ := sourceWalshSum_recorded_interleaved p l fuel hdegree hbound
  obtain ⟨m, hdim⟩ := recordedCoordinateOrder_dimension pairs hlen
  have hsize : n = (pairs.length + pairs.length) + m := by omega
  refine ⟨hlen, m, hsize, ?_⟩
  let f := recordedCoordinateAt pairs hlen
  let r := fun x => evalPhase (recordedPairPhase pairs) x
  let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
  let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
  let q := binaryVectorCast hsize (coordinateReindex f t)
  let d := (pairs.length + pairs.length) + m
  let sourceSummand := fun y : BinaryVector n => integerWalshSign
    (Bool.xor
      (pairPhaseEval (List.replicate pairs.length (false, false))
        (vectorPairAssignment
          (fun j : Fin pairs.length => y ⟨2 * j.val, by have hj := j.isLt; omega⟩)
          (fun j : Fin pairs.length => y ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩)) c)
      (walshWireParity (List.finRange n) (coordinateReindex f t) y))
  let genericSummand := fun y : BinaryVector d => integerWalshSign
    (Bool.xor
      (pairPhaseEval (List.replicate pairs.length (false, false))
        (vectorPairAssignment
          (fun j : Fin pairs.length => y ⟨2 * j.val, by have hj := j.isLt; omega⟩)
          (fun j : Fin pairs.length => y ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩))
        (radicalPhaseEval (List.replicate m false)
          (vectorAssignment (fun i : Fin m => y ⟨2 * pairs.length + i.val,
            by have hi := i.isLt; omega⟩)) c))
      (walshWireParity (List.finRange d) q y))
  have hsum' : sourceWalshSum p l = ((binaryBasis n).map sourceSummand).sum := by
    simpa [sourceSummand, f, r, c, a, t] using hsum
  have hleft : 2 * pairs.length ≤ n := by omega
  have hright : 2 * pairs.length ≤ d := by omega
  have hpoint (y : BinaryVector n) :
      sourceSummand y = genericSummand (binaryVectorCast hsize y) := by
    dsimp [sourceSummand, genericSummand]
    apply congrArg integerWalshSign
    rw [interleavedPairAssignment_binaryVectorCast hsize hleft hright y]
    rw [radicalPhaseEval_replicate_false]
    simpa [d, q] using
      (walshWireParity_binaryVectorCast hsize (coordinateReindex f t) y)
  have hwire : sourceWalshSum p l =
      interleavedWireCharacterWalshSum (k := pairs.length) (m := m)
        (List.replicate pairs.length (false, false)) (List.replicate m false) c q := by
    calc
      sourceWalshSum p l = ((binaryBasis n).map sourceSummand).sum := hsum'
      _ = ((binaryBasis n).map (fun y => genericSummand (binaryVectorCast hsize y))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y hy
        exact hpoint y
      _ = ((binaryBasis d).map genericSummand).sum :=
        integerSum_binaryVectorCast hsize genericSummand
      _ = interleavedWireCharacterWalshSum (k := pairs.length) (m := m)
          (List.replicate pairs.length (false, false)) (List.replicate m false) c q := by
        rfl
  rw [hwire]
  have hp : (List.replicate pairs.length (false, false)).length = pairs.length := by simp
  have hb : (List.replicate m false).length = m := by simp
  simpa [q, c, f, r, a, t] using
    (interleavedWireCharacterWalshSum_closed (k := pairs.length) (m := m)
      (List.replicate pairs.length (false, false)) (List.replicate m false) c q hp hb)

/-- The recorded closed form also determines the exact natural absolute value. -/
theorem sourceWalshSum_recorded_interleaved_cast_naturalAbs {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    ∃ hlen : (recordedCoordinateOrder pairs).length = n,
      ∃ m, ∃ hsize : n = (pairs.length + pairs.length) + m,
        let f := recordedCoordinateAt pairs hlen
        let r := fun x => evalPhase (recordedPairPhase pairs) x
        let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
        let a := fun i => normalizedDifference
          (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
        let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
        let q := binaryVectorCast hsize (coordinateReindex f t)
        let canonical := coordinateReindex
          (@interleavedIndexFromCanonical pairs.length m) q
        let ds := vectorAssignment (canonicalRadical canonical)
        Int.natAbs (sourceWalshSum p l) =
          if (radicalCoefficientsXor (List.replicate m false) ds).any id then 0
          else 2 ^ (m + pairs.length) := by
  obtain ⟨hlen, m, hsize, hclosed⟩ :=
    sourceWalshSum_recorded_interleaved_cast_closed p l fuel hdegree hbound
  refine ⟨hlen, m, hsize, ?_⟩
  dsimp only
  rw [hclosed]
  split_ifs
  · simp
  · simp [Int.natAbs_mul, integerWalshSign_naturalAbs]

/-- The magnitude formula is independent of which valid dimension witnesses are chosen. -/
theorem sourceWalshSum_recorded_interleaved_cast_naturalAbs_of_witness {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    let f := recordedCoordinateAt pairs hlen
    let r := fun x => evalPhase (recordedPairPhase pairs) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    let q := binaryVectorCast hsize (coordinateReindex f t)
    let canonical := coordinateReindex
      (@interleavedIndexFromCanonical pairs.length m) q
    let ds := vectorAssignment (canonicalRadical canonical)
    Int.natAbs (sourceWalshSum p l) =
      if (radicalCoefficientsXor (List.replicate m false) ds).any id then 0
      else 2 ^ (m + pairs.length) := by
  obtain ⟨hlen', m', hsize', hformula⟩ :=
    sourceWalshSum_recorded_interleaved_cast_naturalAbs p l fuel hdegree hbound
  have hm : m' = m := by omega
  subst m'
  have hproof : hlen' = hlen := Subsingleton.elim _ _
  rw [hproof] at hformula
  have hsizeproof : hsize' = hsize := Subsingleton.elim _ _
  rw [hsizeproof] at hformula
  simpa only using hformula

/-- The polar-elimination coordinates give an exact support test for the source Walsh sum. -/
theorem sourceWalshSum_recorded_interleaved_cast_zero_iff_of_witness {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    let f := recordedCoordinateAt pairs hlen
    let r := fun x => evalPhase (recordedPairPhase pairs) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    let q := binaryVectorCast hsize (coordinateReindex f t)
    let canonical := coordinateReindex
      (@interleavedIndexFromCanonical pairs.length m) q
    let ds := vectorAssignment (canonicalRadical canonical)
    (sourceWalshSum p l = 0) ↔
      (radicalCoefficientsXor (List.replicate m false) ds).any id = true := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  let f := recordedCoordinateAt pairs hlen
  let r := fun x => evalPhase (recordedPairPhase pairs) x
  let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
  let a := fun i => normalizedDifference
    (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
  let q := binaryVectorCast hsize (coordinateReindex f t)
  let canonical := coordinateReindex (@interleavedIndexFromCanonical pairs.length m) q
  let ds := vectorAssignment (canonicalRadical canonical)
  let support := (radicalCoefficientsXor (List.replicate m false) ds).any id
  change (sourceWalshSum p l = 0) ↔ support = true
  have habs : Int.natAbs (sourceWalshSum p l) =
      if support then 0 else 2 ^ (m + pairs.length) := by
    simpa [out, pairs, f, r, c, a, t, q, canonical, ds, support] using
      (sourceWalshSum_recorded_interleaved_cast_naturalAbs_of_witness
        p l fuel hdegree hbound hlen m hsize)
  have hzero : sourceWalshSum p l = 0 ↔ Int.natAbs (sourceWalshSum p l) = 0 := by simp
  rw [hzero, habs]
  have hp : 0 < 2 ^ (m + pairs.length) := Nat.pow_pos (by decide)
  cases hsupport : support <;> simp [hsupport, Nat.ne_of_gt hp]

/-- The support test is equivalent to a nonzero value at an individual residual coordinate. -/
theorem sourceWalshSum_recorded_interleaved_cast_zero_iff_residualCoordinate {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    let f := recordedCoordinateAt pairs hlen
    let r := fun x => evalPhase (recordedPairPhase pairs) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    let q := binaryVectorCast hsize (coordinateReindex f t)
    let canonical := coordinateReindex
      (@interleavedIndexFromCanonical pairs.length m) q
    (sourceWalshSum p l = 0) ↔ ∃ i : Fin m, canonicalRadical canonical i = true := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  let f := recordedCoordinateAt pairs hlen
  let r := fun x => evalPhase (recordedPairPhase pairs) x
  let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
  let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
  let q := binaryVectorCast hsize (coordinateReindex f t)
  let canonical := coordinateReindex (@interleavedIndexFromCanonical pairs.length m) q
  have h := sourceWalshSum_recorded_interleaved_cast_zero_iff_of_witness
    p l fuel hdegree hbound hlen m hsize
  dsimp only [out, pairs, f, r, c, a, t, q, canonical] at h ⊢
  exact h.trans (radicalCoefficientsXor_replicate_false_any (canonicalRadical canonical))

/-- Residual coordinates of an affine transformed character, after recorded and
interleaved coordinate changes. -/
def recordedResidualCoordinates {n k m : Nat} (f : Fin n → Fin n)
    (h : n = (k + k) + m) (a : BinaryVector n) (T : BinaryMatrix n)
    (l : BinaryVector n) : BinaryVector m :=
  canonicalRadical (@coordinateReindex ((k + k) + m)
    (@interleavedIndexFromCanonical k m)
    (binaryVectorCast h (coordinateReindex f (binaryShift a (matrixApply T l)))))

/-- The residual offset induced by the fixed affine character. -/
def recordedResidualOffset {n k m : Nat} (f : Fin n → Fin n)
    (h : n = (k + k) + m) (a : BinaryVector n) : BinaryVector m :=
  canonicalRadical (@coordinateReindex ((k + k) + m)
    (@interleavedIndexFromCanonical k m)
    (binaryVectorCast h (coordinateReindex f a)))

/-- The linear residual-coordinate part of the transformed wire character. -/
def recordedResidualLinearPart {n k m : Nat} (f : Fin n → Fin n)
    (h : n = (k + k) + m) (T : BinaryMatrix n)
    (l : BinaryVector n) : BinaryVector m :=
  canonicalRadical (@coordinateReindex ((k + k) + m)
    (@interleavedIndexFromCanonical k m)
    (binaryVectorCast h (coordinateReindex f (matrixApply T l))))

theorem recordedResidualCoordinates_eq_offset_xor_linearPart {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (a : BinaryVector n)
    (T : BinaryMatrix n) (l : BinaryVector n) :
    recordedResidualCoordinates f h a T l =
      vectorXor (recordedResidualLinearPart f h T l) (recordedResidualOffset f h a) := by
  funext i
  simp [recordedResidualCoordinates, recordedResidualOffset, recordedResidualLinearPart,
    canonicalRadical, coordinateReindex, binaryVectorCast, binaryShift, vectorXor]

theorem recordedResidualLinearPart_vectorXor {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (T : BinaryMatrix n)
    (x y : BinaryVector n) :
    recordedResidualLinearPart f h T (vectorXor x y) =
      vectorXor (recordedResidualLinearPart f h T x) (recordedResidualLinearPart f h T y) := by
  funext i
  simp [recordedResidualLinearPart, canonicalRadical, coordinateReindex,
    binaryVectorCast, vectorXor, matrixApply_xor]

theorem recordedResidualLinearPart_zeroVector {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (T : BinaryMatrix n) :
    recordedResidualLinearPart f h T zeroVector = zeroVector := by
  funext i
  simp [recordedResidualLinearPart, canonicalRadical, coordinateReindex,
    binaryVectorCast, zeroVector, matrixApply_zero]

theorem recordedResidualLinearPart_surjective {n k m : Nat}
    (f : Fin n → Fin n) (hf : Function.Bijective f)
    (h : n = (k + k) + m) (T : BinaryMatrix n)
    (hT : Function.Surjective (matrixApply T)) :
    Function.Surjective (recordedResidualLinearPart f h T) := by
  cases h
  intro w
  let canonical : BinaryVector ((k + k) + m) := canonicalJoin zeroVector zeroVector w
  let interleaved := interleavedVectorOfCanonical canonical
  let finv := coordinateInverse f hf.2
  let preimage := coordinateReindex finv interleaved
  obtain ⟨x, hx⟩ := hT preimage
  refine ⟨x, ?_⟩
  have hreindex : coordinateReindex f (coordinateReindex finv interleaved) = interleaved := by
    funext i
    change interleaved (finv (f i)) = interleaved i
    exact congrArg interleaved (coordinateInverse_left f hf.1 hf.2 i)
  change canonicalRadical (@coordinateReindex ((k + k) + m)
    (@interleavedIndexFromCanonical k m) (coordinateReindex f (matrixApply T x))) = w
  rw [hx, hreindex]
  rw [← canonicalBlockOfInterleaved_coordinateReindex]
  rw [canonicalBlockOfInterleaved_rightInverse]
  exact canonicalRadical_join zeroVector zeroVector w

theorem vectorXor_eq_zero_iff {m : Nat} (x y : BinaryVector m) :
    vectorXor x y = zeroVector ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    cases hx : x i <;> cases hy : y i <;>
      simp [vectorXor, zeroVector, hx, hy] at hi ⊢
  · rintro rfl
    funext i
    simp [vectorXor, zeroVector]

theorem recordedResidualCoordinates_eq_zero_iff_linearPart_eq_offset {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (a : BinaryVector n)
    (T : BinaryMatrix n) (l : BinaryVector n) :
    recordedResidualCoordinates f h a T l = zeroVector ↔
      recordedResidualLinearPart f h T l = recordedResidualOffset f h a := by
  rw [recordedResidualCoordinates_eq_offset_xor_linearPart]
  exact vectorXor_eq_zero_iff _ _

/-- Nonzero source-Walsh support is exactly the simultaneous vanishing of every
residual transformed-character coordinate. -/
theorem sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_residualCoordinates_zero {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    let f := recordedCoordinateAt pairs hlen
    let r := fun x => evalPhase (recordedPairPhase pairs) x
    let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
    let a := fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply out.1 y))
      (fun y => evalPhase (recordedPairPhase pairs) y) (coordinateUnit i)
    let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
    let q := binaryVectorCast hsize (coordinateReindex f t)
    let canonical := coordinateReindex
      (@interleavedIndexFromCanonical pairs.length m) q
    sourceWalshSum p l ≠ 0 ↔ ∀ i : Fin m, canonicalRadical canonical i = false := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  let f := recordedCoordinateAt pairs hlen
  let r := fun x => evalPhase (recordedPairPhase pairs) x
  let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
  let a := fun i => normalizedDifference
    (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
  let q := binaryVectorCast hsize (coordinateReindex f t)
  let canonical := coordinateReindex (@interleavedIndexFromCanonical pairs.length m) q
  have hzero := sourceWalshSum_recorded_interleaved_cast_zero_iff_residualCoordinate
    p l fuel hdegree hbound hlen m hsize
  dsimp only [out, pairs, f, r, c, a, t, q, canonical] at hzero ⊢
  have hzero' : sourceWalshSum p l = 0 ↔
      ∃ i : Fin m, canonicalRadical canonical i = true := by
    simpa [canonical] using hzero
  change (¬ sourceWalshSum p l = 0) ↔
    ∀ i : Fin m, canonicalRadical canonical i = false
  rw [hzero']
  constructor
  · intro h i
    cases hi : canonicalRadical canonical i with
    | false => rfl
    | true => exact False.elim (h ⟨i, hi⟩)
  · intro h hex
    rcases hex with ⟨i, hi⟩
    rw [h i] at hi
    cases hi

theorem sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_affineResidualEquation {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    let f := recordedCoordinateAt pairs hlen
    let a := fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply out.1 y))
      (fun y => evalPhase (recordedPairPhase pairs) y) (coordinateUnit i)
    sourceWalshSum p l ≠ 0 ↔
      recordedResidualLinearPart f hsize (transposeBinaryMatrix out.1) l =
        recordedResidualOffset f hsize a := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  let f := recordedCoordinateAt pairs hlen
  let a := fun i => normalizedDifference
    (fun y => evalPhase p (matrixApply out.1 y))
    (fun y => evalPhase (recordedPairPhase pairs) y) (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
  let q := binaryVectorCast hsize (coordinateReindex f t)
  let canonical := coordinateReindex (@interleavedIndexFromCanonical pairs.length m) q
  let coordinates := recordedResidualCoordinates f hsize a (transposeBinaryMatrix out.1) l
  have hsupport := sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_residualCoordinates_zero
    p l fuel hdegree hbound hlen m hsize
  have hcoordinates : coordinates = canonicalRadical canonical := by
    rfl
  have hzero : coordinates = zeroVector ↔
      ∀ i : Fin m, canonicalRadical canonical i = false := by
    constructor
    · intro hz i
      have hi := congrFun (hcoordinates ▸ hz) i
      simpa [zeroVector] using hi
    · intro hi
      rw [hcoordinates]
      funext i
      simpa [zeroVector] using hi i
  dsimp only [out, pairs, f, a, t, q, canonical] at hsupport ⊢
  calc
    sourceWalshSum p l ≠ 0 ↔ coordinates = zeroVector := by
      exact hsupport.trans hzero.symm
    _ ↔ recordedResidualLinearPart f hsize (transposeBinaryMatrix out.1) l =
          recordedResidualOffset f hsize a :=
      recordedResidualCoordinates_eq_zero_iff_linearPart_eq_offset f hsize a
        (transposeBinaryMatrix out.1) l


/-- The exact quadratic Walsh formula is bounded by the size of its input space. -/
theorem sourceWalshSum_recorded_interleaved_cast_abs_le_two_pow {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    Int.natAbs (sourceWalshSum p l) ≤ 2 ^ n := by
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
  let pairs := out.2.2
  have hexact := sourceWalshSum_recorded_interleaved_cast_naturalAbs
    p l fuel hdegree hbound
  dsimp only [out, pairs] at hexact
  obtain ⟨hlen, m, hsize, habs⟩ := hexact
  have hpairs :
      ((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length =
        pairs.length := by rfl
  rw [hpairs] at hsize
  have hmn : m + pairs.length ≤ n := by omega
  rw [habs]
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) hmn

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


theorem matrixApply_surjective_of_injective {n : Nat} (J : BinaryMatrix n)
    (hJ : Function.Injective (matrixApply J)) : Function.Surjective (matrixApply J) := by
  obtain ⟨ops, hops⟩ := gaussianRowProgram_exists_of_injective J hJ
  intro y
  exact ⟨runCNOTs (rowProgramCNOTs ops) y, matrixApply_inverse_forward J ops hops y⟩

/-- Pairing a character against a coordinate unit reads off that coordinate. -/
theorem walshWireParity_coordinateUnit {n : Nat} (v : BinaryVector n) (i : Fin n) :
    walshWireParity (List.finRange n) v (coordinateUnit i) = v i := by
  rw [walshWireParity_as_sum]
  have hfun : (fun j => v j && coordinateUnit i j)
      = (fun j => decide (j = i) && v j) := by
    funext j
    simp only [coordinateUnit]
    exact Bool.and_comm (v j) (decide (j = i))
  rw [hfun, booleanListSum_singleton _ i v (List.nodup_finRange n)]
  simp

theorem matrixApply_transpose_injective_of_surjective {n : Nat} (J : BinaryMatrix n)
    (hJ : Function.Surjective (matrixApply J)) :
    Function.Injective (matrixApply (transposeBinaryMatrix J)) := by
  intro x y hxy
  funext i
  have hxunit : walshWireParity (List.finRange n) x (coordinateUnit i) = x i :=
    walshWireParity_coordinateUnit x i
  have hyunit : walshWireParity (List.finRange n) y (coordinateUnit i) = y i :=
    walshWireParity_coordinateUnit y i
  obtain ⟨z, hz⟩ := hJ (coordinateUnit i)
  have hp : walshWireParity (List.finRange n) x (coordinateUnit i) =
      walshWireParity (List.finRange n) y (coordinateUnit i) := by
    calc
      walshWireParity (List.finRange n) x (coordinateUnit i) =
          walshWireParity (List.finRange n) x (matrixApply J z) := by rw [hz]
      _ = walshWireParity (List.finRange n) (matrixApply (transposeBinaryMatrix J) x) z :=
          binaryTranspose_character J x z
      _ = walshWireParity (List.finRange n) (matrixApply (transposeBinaryMatrix J) y) z := by rw [hxy]
      _ = walshWireParity (List.finRange n) y (matrixApply J z) :=
          (binaryTranspose_character J y z).symm
      _ = walshWireParity (List.finRange n) y (coordinateUnit i) := by rw [hz]
  rw [hxunit, hyunit] at hp
  exact hp

theorem matrixApply_transpose_surjective_of_injective {n : Nat} (J : BinaryMatrix n)
    (hJ : Function.Injective (matrixApply J)) :
    Function.Surjective (matrixApply (transposeBinaryMatrix J)) := by
  apply matrixApply_surjective_of_injective
  exact matrixApply_transpose_injective_of_surjective J (matrixApply_surjective_of_injective J hJ)

theorem polarEliminate_transpose_surjective {n : Nat}
    (B : BinaryVector n → BinaryVector n → Bool) (fuel : Nat)
    (indices : List (Fin n)) :
    Function.Surjective (matrixApply (transposeBinaryMatrix
      (polarEliminate B fuel indices identityMatrix).1)) := by
  apply matrixApply_transpose_surjective_of_injective
  intro x y hxy
  have hid : Function.Injective (matrixApply (identityMatrix : BinaryMatrix n)) := by
    intro a b hab
    simpa [matrixApply_identity] using hab
  exact polarEliminate_preserves_injective B fuel indices (identityMatrix : BinaryMatrix n) hid hxy

theorem recordedResidualLinearPart_surjective_for_polarEliminate {n k m : Nat}
    (f : Fin n → Fin n) (hf : Function.Bijective f)
    (h : n = (k + k) + m) (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) :
    Function.Surjective (recordedResidualLinearPart f h
      (transposeBinaryMatrix (polarEliminate B fuel indices identityMatrix).1)) := by
  exact recordedResidualLinearPart_surjective f hf h _
    (polarEliminate_transpose_surjective B fuel indices)

/-- The recorded coordinate map of the actual source construction is bijective:
polar elimination records distinct, pairwise disjoint endpoint pairs, so the
recorded coordinate order is a permutation of the index list. -/
theorem sourceRecordedCoordinateAt_bijective {n : Nat}
    (p : PhaseANF n) (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n) :
    Function.Bijective (recordedCoordinateAt
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) := by
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl : ∀ x, phasePolar p x x = false := by
    intro x
    rw [hpolar]
    exact halt x
  have hd := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl
  have hb := recordedCoordinateAt_bijective
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hd.1 hd.2
  exact ⟨hb.1, hb.2⟩

/-- Surjectivity of the residual linear-character projection for the actual source
construction, with no assumed coordinate bijectivity or matrix hypothesis. -/
theorem sourceRecordedResidualLinearPart_surjective {n : Nat}
    (p : PhaseANF n) (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    Function.Surjective (recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)) := by
  exact recordedResidualLinearPart_surjective_for_polarEliminate _
    (sourceRecordedCoordinateAt_bijective p fuel hdegree hlen) hsize
    (phasePolar p) fuel (List.finRange n)

/-- The exact source Walsh support is nonempty: for every degree-at-most-two source
phase there is a wire character whose exact source Walsh sum is nonzero. -/
theorem sourceWalshSum_support_nonempty {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    ∃ l : BinaryVector n, sourceWalshSum p l ≠ 0 := by
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl : ∀ x, phasePolar p x x = false := by
    intro x
    rw [hpolar]
    exact halt x
  have hd := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl
  have hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n := by
    simpa using (recordedCoordinateOrder_perm
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
      hd.1 hd.2).length_eq
  obtain ⟨m, hdim⟩ := recordedCoordinateOrder_dimension
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen
  have hsize : n =
      (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m) := by
    omega
  have hsurj := sourceRecordedResidualLinearPart_surjective p fuel hdegree hlen m hsize
  obtain ⟨l, hsolution⟩ := hsurj (recordedResidualOffset
    (recordedCoordinateAt
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
    hsize
    (fun i => normalizedDifference
      (fun y => evalPhase p (matrixApply
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y))
      (fun y => evalPhase (recordedPairPhase
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) y)
      (coordinateUnit i)))
  refine ⟨l, ?_⟩
  exact (sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_affineResidualEquation
    p l fuel hdegree hbound hlen m hsize).mpr hsolution

/-- The source coordinate index carrying the `i`-th residual coordinate. -/
def recordedRadicalIndex {n k m : Nat} (f : Fin n → Fin n) (h : n = (k + k) + m)
    (i : Fin m) : Fin n :=
  f (Fin.cast h.symm (@interleavedIndexFromCanonical k m (Fin.natAdd (k + k) i)))

/-- Each residual coordinate is one source coordinate of the transformed character. -/
theorem recordedResidualLinearPart_apply_radicalIndex {n k m : Nat} (f : Fin n → Fin n)
    (h : n = (k + k) + m) (T : BinaryMatrix n) (l : BinaryVector n) (i : Fin m) :
    recordedResidualLinearPart f h T l i =
      matrixApply T l (recordedRadicalIndex f h i) := rfl

/-- On the radical block the interleaved layout permutation is the identity, so the
residual indices are the recorded coordinates in positions `k + k` onward. -/
theorem recordedRadicalIndex_eq_cast_natAdd {n k m : Nat} (f : Fin n → Fin n)
    (h : n = (k + k) + m) (i : Fin m) :
    recordedRadicalIndex f h i = f (Fin.cast h.symm (Fin.natAdd (k + k) i)) := by
  unfold recordedRadicalIndex
  apply congrArg f
  apply congrArg (Fin.cast h.symm)
  unfold interleavedIndexFromCanonical
  have hleft : ¬ ((Fin.natAdd (k + k) i : Fin ((k + k) + m)).val < k) := by
    simp only [Fin.natAdd]
    omega
  have hright : ¬ ((Fin.natAdd (k + k) i : Fin ((k + k) + m)).val < k + k) := by
    simp only [Fin.natAdd]
    omega
  rw [dif_neg hleft, dif_neg hright]

/-- The kernel of the residual projection is cut out by `m` explicit source
coordinate equations on the transformed character. -/
theorem recordedResidualLinearPart_eq_zero_iff_radicalCoordinates {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (T : BinaryMatrix n) (l : BinaryVector n) :
    recordedResidualLinearPart f h T l = zeroVector ↔
      ∀ i : Fin m, matrixApply T l (recordedRadicalIndex f h i) = false := by
  constructor
  · intro hz i
    have hi := congrFun hz i
    rw [recordedResidualLinearPart_apply_radicalIndex] at hi
    simpa [zeroVector] using hi
  · intro hi
    funext i
    rw [recordedResidualLinearPart_apply_radicalIndex]
    simpa [zeroVector] using hi i

/-- Two characters have the same residual image exactly when their difference lies in
the kernel. This is the coset law of the residual projection. -/
theorem recordedResidualLinearPart_eq_iff_vectorXor_kernel {n k m : Nat}
    (f : Fin n → Fin n) (h : n = (k + k) + m) (T : BinaryMatrix n)
    (x y : BinaryVector n) :
    recordedResidualLinearPart f h T x = recordedResidualLinearPart f h T y ↔
      recordedResidualLinearPart f h T (vectorXor x y) = zeroVector := by
  rw [recordedResidualLinearPart_vectorXor]
  exact (vectorXor_eq_zero_iff (recordedResidualLinearPart f h T x)
    (recordedResidualLinearPart f h T y)).symm

/-- The exact source Walsh support is a coset of the residual kernel: once one wire
character has nonzero source Walsh sum, another does exactly when their difference
lies in the kernel of the residual projection. -/
theorem sourceWalshSum_support_coset {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l l' : BinaryVector n) (hne : sourceWalshSum p l ≠ 0) :
    sourceWalshSum p l' ≠ 0 ↔
      recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (vectorXor l l') = zeroVector := by
  have hiff := sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_affineResidualEquation
    p l fuel hdegree hbound hlen m hsize
  have hiff' := sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_affineResidualEquation
    p l' fuel hdegree hbound hlen m hsize
  have hl := hiff.mp hne
  constructor
  · intro hne'
    exact (recordedResidualLinearPart_eq_iff_vectorXor_kernel _ hsize _ l l').mp
      (hl.trans (hiff'.mp hne').symm)
  · intro hker
    have heq := (recordedResidualLinearPart_eq_iff_vectorXor_kernel _ hsize _ l l').mpr hker
    exact hiff'.mpr (heq.symm.trans hl)

/-- The radical indices are exactly the unpaired indices of the polar elimination:
the recorded coordinate order lists the pair endpoints first, so positions from twice
the pair count onward are the unpaired block. -/
theorem recordedRadicalIndex_mem_unpairedIndices {n m : Nat}
    (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hsize : n = (pairs.length + pairs.length) + m) (i : Fin m) :
    recordedRadicalIndex (recordedCoordinateAt pairs hlen) hsize i
      ∈ unpairedIndices (List.finRange n) pairs := by
  rw [recordedRadicalIndex_eq_cast_natAdd]
  have hep : (pairs.flatMap (fun p => [p.1, p.2])).length = pairs.length + pairs.length := by
    rw [pairEndpoints_length]
    omega
  have hidx : (Fin.cast hsize.symm (Fin.natAdd (pairs.length + pairs.length) i)).val
      = (pairs.length + pairs.length) + i.val := rfl
  show (recordedCoordinateOrder pairs).get
    ⟨(Fin.cast hsize.symm (Fin.natAdd (pairs.length + pairs.length) i)).val, _⟩ ∈ _
  rw [List.get_eq_getElem]
  simp only [hidx, recordedCoordinateOrder]
  rw [List.getElem_append_right (by omega)]
  exact List.getElem_mem _

/-- The source polar form as a vector of coordinate pairings. -/
def sourcePolarVector {n : Nat} (p : PhaseANF n) (x : BinaryVector n) : BinaryVector n :=
  fun i => phasePolar p x (coordinateUnit i)

/-- The polar vector represents the polar functional through Walsh pairing. -/
theorem sourcePolar_walsh_representation {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) (x y : BinaryVector n) :
    phasePolar p x y = walshWireParity (List.finRange n) (sourcePolarVector p x) y := by
  obtain ⟨ts, _, _, hp, _, _, hright⟩ := sourceQuadratic_hasPolar p hdegree
  have hadd : ∀ u v, phasePolar p x (binaryShift u v)
      = Bool.xor (phasePolar p x u) (phasePolar p x v) := by
    intro u v
    rw [hp, hp, hp]
    exact hright x u v
  have hzero : phasePolar p x (fun _ => false) = false := by
    have h := hadd (fun _ => false) (fun _ => false)
    have hb : binaryShift (fun _ : Fin n => false) (fun _ => false)
        = (fun _ : Fin n => false) := by
      funext i
      simp [binaryShift]
    rw [hb] at h
    simpa using h
  exact additive_coordinates (fun z => phasePolar p x z) hadd hzero y

/-- A transpose coordinate is the character paired against the matching column. -/
theorem matrixApply_transpose_apply_column {n : Nat} (J : BinaryMatrix n)
    (l : BinaryVector n) (u : Fin n) :
    matrixApply (transposeBinaryMatrix J) l u =
      walshWireParity (List.finRange n) l (matrixColumn J u) := by
  rw [← matrixApply_coordinateUnit, binaryTranspose_character,
    walshWireParity_coordinateUnit]

/-- The pair polar form vanishes against any unpaired coordinate unit, for every
first argument. -/
theorem recordedPairPolar_right_unit_absent {n : Nat} (pairs : List (Fin n × Fin n))
    (u : BinaryVector n) (j : Fin n) (h : ∀ p ∈ pairs, j ≠ p.1 ∧ j ≠ p.2) :
    recordedPairPolar pairs u (coordinateUnit j) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    have htail : ∀ q ∈ ps, j ≠ q.1 ∧ j ≠ q.2 := by
      intro q hq
      exact h q (by simp [hq])
    have h1 : coordinateUnit j p.2 = false := by
      simp only [coordinateUnit, decide_eq_false_iff_not]
      exact fun he => hp.2 he.symm
    have h2 : coordinateUnit j p.1 = false := by
      simp only [coordinateUnit, decide_eq_false_iff_not]
      exact fun he => hp.1 he.symm
    simp [recordedPairPolar, h1, h2, ih htail]

/-- The polar-elimination matrix action is surjective. -/
theorem polarEliminate_surjective {n : Nat}
    (B : BinaryVector n → BinaryVector n → Bool) (fuel : Nat) (indices : List (Fin n)) :
    Function.Surjective (matrixApply (polarEliminate B fuel indices identityMatrix).1) := by
  apply matrixApply_surjective_of_injective
  intro x y hxy
  have hid : Function.Injective (matrixApply (identityMatrix : BinaryMatrix n)) := by
    intro a b hab
    simpa [matrixApply_identity] using hab
  exact polarEliminate_preserves_injective B fuel indices (identityMatrix : BinaryMatrix n) hid hxy

/-- Every source polar vector lies in the kernel of the residual projection: the image
of the source quadratic polar form is contained in the kernel that cuts out the exact
source Walsh support. -/
theorem sourcePolarVector_mem_residualKernel {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (x : BinaryVector n) :
    recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (sourcePolarVector p x) = zeroVector := by
  rw [recordedResidualLinearPart_eq_zero_iff_radicalCoordinates]
  intro i
  have humem := recordedRadicalIndex_mem_unpairedIndices
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize i
  rw [matrixApply_transpose_apply_column, ← sourcePolar_walsh_representation p hdegree]
  obtain ⟨w, hw⟩ := polarEliminate_surjective (phasePolar p) fuel (List.finRange n) x
  rw [← hw, ← matrixApply_coordinateUnit,
    sourcePolar_all_vectors p fuel identityMatrix hdegree hbound,
    recordedPairPhase_polar]
  exact recordedPairPolar_right_unit_absent _ w _
    (unpairedIndices_absent (List.finRange n) _ _ humem)

/-- Boolean identity behind additivity of the pair form in its second argument. -/
theorem bool_recordedPair_xor (a b v1 v2 w1 w2 tv tw : Bool) :
    Bool.xor (Bool.xor (a && Bool.xor w2 v2) (b && Bool.xor w1 v1)) (Bool.xor tv tw)
      = Bool.xor (Bool.xor (Bool.xor (a && v2) (b && v1)) tv)
          (Bool.xor (Bool.xor (a && w2) (b && w1)) tw) := by
  cases a <;> cases b <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    cases tv <;> cases tw <;> rfl

theorem recordedPairPolar_right_zero {n : Nat} (pairs : List (Fin n × Fin n))
    (u : BinaryVector n) :
    recordedPairPolar pairs u (fun _ => false) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp [recordedPairPolar, ih]

/-- The pair form is additive in its second argument. -/
theorem recordedPairPolar_right_xor {n : Nat} (pairs : List (Fin n × Fin n))
    (u v w : BinaryVector n) :
    recordedPairPolar pairs u (binaryShift v w)
      = Bool.xor (recordedPairPolar pairs u v) (recordedPairPolar pairs u w) := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [recordedPairPolar, ih, binaryShift]
    exact bool_recordedPair_xor (u p.1) (u p.2) (v p.1) (v p.2) (w p.1) (w p.2)
      (recordedPairPolar ps u v) (recordedPairPolar ps u w)

/-- The pair form in its second argument is represented by its coordinate vector. -/
theorem recordedPairPolar_right_representation {n : Nat} (pairs : List (Fin n × Fin n))
    (u v : BinaryVector n) :
    recordedPairPolar pairs u v
      = walshWireParity (List.finRange n)
          (fun i => recordedPairPolar pairs u (coordinateUnit i)) v :=
  additive_coordinates (fun z => recordedPairPolar pairs u z)
    (fun a b => recordedPairPolar_right_xor pairs u a b)
    (recordedPairPolar_right_zero pairs u) v

/-- At the first endpoint of a recorded pair the form reads the partner coordinate. -/
theorem recordedPairPolar_right_member_first {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (u : BinaryVector n) (p : Fin n × Fin n) (hp : p ∈ pairs) :
    recordedPairPolar pairs u (coordinateUnit p.1) = u p.2 := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    have hcons := List.pairwise_cons.mp hd
    have htail : ∀ r ∈ qs, r.1 ≠ r.2 := by
      intro r hr
      exact hne r (by simp [hr])
    simp only [List.mem_cons] at hp
    rcases hp with he | hm
    · subst q
      have hz : recordedPairPolar qs u (coordinateUnit p.1) = false := by
        apply recordedPairPolar_right_unit_absent
        intro r hr
        have hdd := hcons.1 r hr
        exact ⟨Ne.symm hdd.1, Ne.symm hdd.2.2.1⟩
      simp [recordedPairPolar, coordinateUnit, Ne.symm (hne p (by simp)), hz]
    · have hdis := hcons.1 p hm
      have hrec := ih hcons.2 htail hm
      simp [recordedPairPolar, coordinateUnit, Ne.symm hdis.1, Ne.symm hdis.2.1, hrec]

/-- At the second endpoint of a recorded pair the form reads the partner coordinate. -/
theorem recordedPairPolar_right_member_second {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (u : BinaryVector n) (p : Fin n × Fin n) (hp : p ∈ pairs) :
    recordedPairPolar pairs u (coordinateUnit p.2) = u p.1 := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    have hcons := List.pairwise_cons.mp hd
    have htail : ∀ r ∈ qs, r.1 ≠ r.2 := by
      intro r hr
      exact hne r (by simp [hr])
    simp only [List.mem_cons] at hp
    rcases hp with he | hm
    · subst q
      have hz : recordedPairPolar qs u (coordinateUnit p.2) = false := by
        apply recordedPairPolar_right_unit_absent
        intro r hr
        have hdd := hcons.1 r hr
        exact ⟨Ne.symm hdd.2.1, Ne.symm hdd.2.2.2⟩
      simp [recordedPairPolar, coordinateUnit, hne p (by simp), hz]
    · have hdis := hcons.1 p hm
      have hrec := ih hcons.2 htail hm
      simp [recordedPairPolar, coordinateUnit, Ne.symm hdis.2.2.1, Ne.symm hdis.2.2.2, hrec]

/-- The partner vector of a residual coordinate vector: each pair endpoint receives the
value the vector assigns to its partner. -/
def pairPartnerVector {n : Nat} (pairs : List (Fin n × Fin n))
    (c : BinaryVector n) : BinaryVector n :=
  fun j => (pairs.map (fun p =>
    Bool.xor (decide (j = p.1) && c p.2) (decide (j = p.2) && c p.1))).foldr Bool.xor false

theorem pairPartnerVector_absent {n : Nat} (pairs : List (Fin n × Fin n))
    (c : BinaryVector n) (j : Fin n) (h : ∀ p ∈ pairs, j ≠ p.1 ∧ j ≠ p.2) :
    pairPartnerVector pairs c j = false := by
  unfold pairPartnerVector
  induction pairs with
  | nil => rfl
  | cons q qs ih =>
    have hq := h q (by simp)
    have htail : ∀ r ∈ qs, j ≠ r.1 ∧ j ≠ r.2 := by
      intro r hr
      exact h r (by simp [hr])
    simp [hq.1, hq.2, ih htail]

theorem pairPartnerVector_first {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (c : BinaryVector n) (p : Fin n × Fin n) (hp : p ∈ pairs) :
    pairPartnerVector pairs c p.1 = c p.2 := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    have hcons := List.pairwise_cons.mp hd
    have htail : ∀ r ∈ qs, r.1 ≠ r.2 := by
      intro r hr
      exact hne r (by simp [hr])
    simp only [List.mem_cons] at hp
    rcases hp with he | hm
    · subst q
      have hz : pairPartnerVector qs c p.1 = false := by
        apply pairPartnerVector_absent
        intro r hr
        have hdd := hcons.1 r hr
        exact ⟨Ne.symm hdd.1, Ne.symm hdd.2.2.1⟩
      have hz' := hz
      unfold pairPartnerVector at hz' ⊢
      simp [hne p (by simp), hz']
    · have hdis := hcons.1 p hm
      have hrec := ih hcons.2 htail hm
      have hrec' := hrec
      unfold pairPartnerVector at hrec' ⊢
      simp [hdis.1, hdis.2.1, hrec']

theorem pairPartnerVector_second {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (c : BinaryVector n) (p : Fin n × Fin n) (hp : p ∈ pairs) :
    pairPartnerVector pairs c p.2 = c p.1 := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    have hcons := List.pairwise_cons.mp hd
    have htail : ∀ r ∈ qs, r.1 ≠ r.2 := by
      intro r hr
      exact hne r (by simp [hr])
    simp only [List.mem_cons] at hp
    rcases hp with he | hm
    · subst q
      have hz : pairPartnerVector qs c p.2 = false := by
        apply pairPartnerVector_absent
        intro r hr
        have hdd := hcons.1 r hr
        exact ⟨Ne.symm hdd.2.1, Ne.symm hdd.2.2.2⟩
      have hz' := hz
      unfold pairPartnerVector at hz' ⊢
      simp [Ne.symm (hne p (by simp)), hz']
    · have hdis := hcons.1 p hm
      have hrec := ih hcons.2 htail hm
      have hrec' := hrec
      unfold pairPartnerVector at hrec' ⊢
      simp [hdis.2.2.1, hdis.2.2.2, hrec']

/-- The unpaired block has exactly the residual dimension many indices. -/
theorem unpairedIndices_length_eq_residual {n m : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hsize : n = (pairs.length + pairs.length) + m) :
    (unpairedIndices (List.finRange n) pairs).length = m := by
  have horder : (recordedCoordinateOrder pairs).length
      = 2 * pairs.length + (unpairedIndices (List.finRange n) pairs).length := by
    unfold recordedCoordinateOrder
    rw [List.length_append, pairEndpoints_length]
  omega

/-- Every unpaired index is a radical index, so the residual coordinate equations
constrain the transformed character at every unpaired coordinate. -/
theorem radicalIndex_covers_unpaired {n m : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hsize : n = (pairs.length + pairs.length) + m)
    (j : Fin n) (hj : j ∈ unpairedIndices (List.finRange n) pairs) :
    ∃ i : Fin m, recordedRadicalIndex (recordedCoordinateAt pairs hlen) hsize i = j := by
  have horder : (recordedCoordinateOrder pairs).length
      = 2 * pairs.length + (unpairedIndices (List.finRange n) pairs).length := by
    unfold recordedCoordinateOrder
    rw [List.length_append, pairEndpoints_length]
  have hlenu : (unpairedIndices (List.finRange n) pairs).length = m := by omega
  obtain ⟨k, hklt, hkeq⟩ := List.mem_iff_getElem.mp hj
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [recordedRadicalIndex_eq_cast_natAdd]
  have hunp := recordedCoordinateAt_unpaired pairs hlen k (by omega)
  have hfin : (Fin.cast hsize.symm
      (Fin.natAdd (pairs.length + pairs.length) (⟨k, by omega⟩ : Fin m)))
      = (⟨2 * pairs.length + k, by omega⟩ : Fin n) := by
    apply Fin.ext
    show (pairs.length + pairs.length) + k = 2 * pairs.length + k
    omega
  rw [hfin, hunp, hkeq]

/-- The coordinate vector of the pair form at the partner vector recovers the target
residual coordinate vector, provided the target vanishes on the unpaired block. -/
theorem pairPolar_partner_coordinates {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (c : BinaryVector n)
    (hzero : ∀ j ∈ unpairedIndices (List.finRange n) pairs, c j = false) :
    (fun j => recordedPairPolar pairs (pairPartnerVector pairs c) (coordinateUnit j)) = c := by
  funext j
  by_cases hex : ∃ q ∈ pairs, j = q.1 ∨ j = q.2
  · obtain ⟨q, hq, hcase⟩ := hex
    rcases hcase with h1 | h2
    · subst j
      rw [recordedPairPolar_right_member_first pairs hd hne _ q hq]
      exact pairPartnerVector_second pairs hd hne c q hq
    · subst j
      rw [recordedPairPolar_right_member_second pairs hd hne _ q hq]
      exact pairPartnerVector_first pairs hd hne c q hq
  · have hju : j ∈ unpairedIndices (List.finRange n) pairs := by
      simp [unpairedIndices]
      intro a b hab
      exact ⟨fun he => hex ⟨(a, b), hab, Or.inl he⟩,
        fun he => hex ⟨(a, b), hab, Or.inr he⟩⟩
    rw [recordedPairPolar_right_unit_absent pairs _ j
      (unpairedIndices_absent (List.finRange n) pairs j hju), hzero j hju]

/-- Converse of the kernel inclusion: every character annihilated by the residual
projection is a source polar vector. -/
theorem residualKernel_sub_sourcePolarImage {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l : BinaryVector n)
    (hker : recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector) :
    ∃ x, sourcePolarVector p x = l := by
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl0
  have hc : ∀ j ∈ unpairedIndices (List.finRange n)
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2,
      matrixApply (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l j = false := by
    intro j hj
    obtain ⟨i, hi⟩ := radicalIndex_covers_unpaired
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize j hj
    have hz := (recordedResidualLinearPart_eq_zero_iff_radicalCoordinates _ hsize _ l).mp hker i
    rw [hi] at hz
    exact hz
  refine ⟨matrixApply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
    (pairPartnerVector (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
      (matrixApply (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l)), ?_⟩
  funext i
  obtain ⟨v, hv⟩ := polarEliminate_surjective (phasePolar p) fuel (List.finRange n)
    (coordinateUnit i)
  simp only [sourcePolarVector]
  rw [← hv, sourcePolar_all_vectors p fuel identityMatrix hdegree hbound,
    recordedPairPhase_polar, recordedPairPolar_right_representation,
    pairPolar_partner_coordinates _ hdp.2 hdp.1 _ hc,
    ← binaryTranspose_character, hv, walshWireParity_coordinateUnit]

/-- The kernel of the residual projection is exactly the image of the source quadratic
polar form. -/
theorem residualKernel_eq_sourcePolarImage {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l : BinaryVector n) :
    recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector ↔
      ∃ x, sourcePolarVector p x = l := by
  constructor
  · intro hker
    exact residualKernel_sub_sourcePolarImage p fuel hdegree hbound hlen m hsize l hker
  · intro himage
    obtain ⟨x, hx⟩ := himage
    rw [← hx]
    exact sourcePolarVector_mem_residualKernel p fuel hdegree hbound hlen m hsize x

/-- The exact source Walsh support is a coset of the source quadratic polar image:
given one wire character with nonzero exact source Walsh sum, another has nonzero sum
exactly when their difference is a source polar vector. -/
theorem sourceWalshSum_support_polar_coset {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l l' : BinaryVector n) (hne : sourceWalshSum p l ≠ 0) :
    sourceWalshSum p l' ≠ 0 ↔ ∃ x, sourcePolarVector p x = vectorXor l l' := by
  rw [sourceWalshSum_support_coset p fuel hdegree hbound hlen m hsize l l' hne]
  exact residualKernel_eq_sourcePolarImage p fuel hdegree hbound hlen m hsize (vectorXor l l')

/-- Membership in the residual kernel is exactly vanishing of the transformed character
on the unpaired block. -/
theorem residualKernel_iff_transpose_unpaired_zero {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l : BinaryVector n) :
    recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector ↔
      ∀ j ∈ unpairedIndices (List.finRange n)
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2,
        matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l j = false := by
  rw [recordedResidualLinearPart_eq_zero_iff_radicalCoordinates]
  constructor
  · intro h j hj
    obtain ⟨i, hi⟩ := radicalIndex_covers_unpaired
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize j hj
    rw [← hi]
    exact h i
  · intro h i
    exact h _ (recordedRadicalIndex_mem_unpairedIndices
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize i)

/-- The residual kernel is parametrized by the values of the transformed character on
the paired block: every assignment vanishing on the unpaired block is realized by a
unique kernel element. -/
theorem residualKernel_parametrized_by_pairs {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (c : BinaryVector n)
    (hc : ∀ j ∈ unpairedIndices (List.finRange n)
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2, c j = false) :
    ∃! l, matrixApply (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = c ∧
      recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
        = zeroVector := by
  have hinj : Function.Injective (matrixApply (transposeBinaryMatrix
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)) :=
    matrixApply_transpose_injective_of_surjective _
      (polarEliminate_surjective (phasePolar p) fuel (List.finRange n))
  obtain ⟨l, hl⟩ := polarEliminate_transpose_surjective (phasePolar p) fuel (List.finRange n) c
  refine ⟨l, ⟨hl, ?_⟩, ?_⟩
  · rw [residualKernel_iff_transpose_unpaired_zero p fuel hlen m hsize]
    intro j hj
    rw [hl]
    exact hc j hj
  · intro l' hl'
    exact hinj (hl'.1.trans hl.symm)

/-- The rank of the residual kernel's free coordinate block is twice the recorded pair
count, hence even, and it is the codimension of the residual coordinate space. -/
theorem residualKernel_rank_even {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m)) :
    (unpairedIndices (List.finRange n)
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = m ∧
      (List.finRange n).length - (unpairedIndices (List.finRange n)
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length
        = (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ∧
      ∃ r, (List.finRange n).length - (unpairedIndices (List.finRange n)
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length
        = r + r := by
  have hu := unpairedIndices_length_eq_residual
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize
  have hfr : (List.finRange n).length = n := List.length_finRange
  refine ⟨hu, ?_, ?_⟩
  · rw [hfr, hu]
    omega
  · refine ⟨(polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length, ?_⟩
    rw [hfr, hu]
    omega

/-- Recorded positions below twice the pair count carry pair endpoints. -/
theorem recordedCoordinateAt_mem_endpoints {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n) (t : Fin n)
    (ht : t.val < 2 * pairs.length) :
    ∃ q ∈ pairs, recordedCoordinateAt pairs hlen t = q.1 ∨
      recordedCoordinateAt pairs hlen t = q.2 := by
  have htn := t.isLt
  obtain ⟨s, hslt, hseq⟩ : ∃ s, s < pairs.length ∧ (t.val = 2 * s ∨ t.val = 2 * s + 1) :=
    ⟨t.val / 2, by omega, by omega⟩
  refine ⟨pairs[s], List.getElem_mem hslt, ?_⟩
  rcases hseq with h0 | h1
  · left
    have hval : t = (⟨2 * s, by omega⟩ : Fin n) := by
      apply Fin.ext
      show t.val = 2 * s
      omega
    rw [hval]
    exact recordedCoordinateAt_pair_first pairs hlen s hslt
  · right
    have hval : t = (⟨2 * s + 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      show t.val = 2 * s + 1
      omega
    rw [hval]
    exact recordedCoordinateAt_pair_second pairs hlen s hslt

/-- A pair endpoint is never an unpaired index. -/
theorem recordedCoordinateAt_not_mem_unpaired {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n) (t : Fin n)
    (ht : t.val < 2 * pairs.length) :
    recordedCoordinateAt pairs hlen t ∉ unpairedIndices (List.finRange n) pairs := by
  intro hmem
  obtain ⟨q, hq, hcase⟩ := recordedCoordinateAt_mem_endpoints pairs hlen t ht
  have habs := unpairedIndices_absent (List.finRange n) pairs _ hmem q hq
  rcases hcase with h1 | h2
  · exact habs.1 h1
  · exact habs.2 h2

/-- Every coordinate index is either a recorded pair endpoint or an unpaired index. -/
theorem recordedIndex_paired_or_unpaired {n m : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint)
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hsize : n = (pairs.length + pairs.length) + m) (j : Fin n) :
    (∃ t : Fin n, t.val < 2 * pairs.length ∧ recordedCoordinateAt pairs hlen t = j) ∨
      j ∈ unpairedIndices (List.finRange n) pairs := by
  have hb := recordedCoordinateAt_bijective pairs hd hp
  obtain ⟨t, ht⟩ := hb.2 j
  by_cases hlt : t.val < 2 * pairs.length
  · exact Or.inl ⟨t, hlt, ht⟩
  · refine Or.inr ?_
    have hu := unpairedIndices_length_eq_residual pairs hlen hsize
    have htn := t.isLt
    obtain ⟨i, hilt, hieq⟩ : ∃ i, i < (unpairedIndices (List.finRange n) pairs).length ∧
        t.val = 2 * pairs.length + i :=
      ⟨t.val - 2 * pairs.length, by omega, by omega⟩
    have heq := recordedCoordinateAt_unpaired pairs hlen i hilt
    have hval : t = (⟨2 * pairs.length + i, by omega⟩ : Fin n) := by
      apply Fin.ext
      show t.val = 2 * pairs.length + i
      omega
    rw [← ht, hval, heq]
    exact List.getElem_mem hilt

/-- The paired coordinates determine a residual kernel element: two kernel elements whose
transformed characters agree on every pair endpoint are equal. This is the dimension
bound complementing the parametrization. -/
theorem residualKernel_determined_by_paired_coordinates {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l l' : BinaryVector n)
    (hl : recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector)
    (hl' : recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l' = zeroVector)
    (hagree : ∀ t : Fin n,
      t.val < 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length →
      matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen t)
        = matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l'
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen t)) :
    l = l' := by
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl0
  have hinj : Function.Injective (matrixApply (transposeBinaryMatrix
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)) :=
    matrixApply_transpose_injective_of_surjective _
      (polarEliminate_surjective (phasePolar p) fuel (List.finRange n))
  have hzl := (residualKernel_iff_transpose_unpaired_zero p fuel hlen m hsize l).mp hl
  have hzl' := (residualKernel_iff_transpose_unpaired_zero p fuel hlen m hsize l').mp hl'
  apply hinj
  funext j
  rcases recordedIndex_paired_or_unpaired
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
    hdp.1 hdp.2 hlen hsize j with ⟨t, htlt, htj⟩ | hju
  · rw [← htj]
    exact hagree t htlt
  · rw [hzl j hju, hzl' j hju]

/-- The recorded position of the `i`-th paired coordinate. -/
def recordedPairedPos {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (i : Fin (2 * pairs.length)) : Fin n :=
  recordedCoordinateAt pairs hlen ⟨i.val, by have := i.isLt; omega⟩

theorem recordedPairedPos_injective {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint)
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) :
    Function.Injective (recordedPairedPos pairs hlen hb) := by
  intro i j hij
  have hinj := (recordedCoordinateAt_bijective pairs hd hp).1
  have heq := hinj hij
  have hval : i.val = j.val := by
    have hc := congrArg Fin.val heq
    simpa using hc
  exact Fin.ext hval

theorem recordedPairedPos_not_mem_unpaired {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (i : Fin (2 * pairs.length)) :
    recordedPairedPos pairs hlen hb i ∉ unpairedIndices (List.finRange n) pairs := by
  apply recordedCoordinateAt_not_mem_unpaired
  show i.val < 2 * pairs.length
  exact i.isLt

theorem booleanListSum_const_false {α : Type} (xs : List α) :
    booleanListSum xs (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    show Bool.xor false (booleanListSum rest (fun _ => false)) = false
    rw [ih]
    rfl

/-- Extend an assignment on the paired block to a full character vanishing off the
pairs. This is the preimage construction for the kernel cardinality bijection. -/
def pairedBlockExtend {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (b : Fin (2 * pairs.length) → Bool) : BinaryVector n :=
  fun j => booleanListSum (List.finRange (2 * pairs.length))
    (fun i => decide (recordedPairedPos pairs hlen hb i = j) && b i)

theorem pairedBlockExtend_apply {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint)
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (b : Fin (2 * pairs.length) → Bool)
    (i₀ : Fin (2 * pairs.length)) :
    pairedBlockExtend pairs hlen hb b (recordedPairedPos pairs hlen hb i₀) = b i₀ := by
  unfold pairedBlockExtend
  have hfun : (fun i => decide (recordedPairedPos pairs hlen hb i
        = recordedPairedPos pairs hlen hb i₀) && b i)
      = (fun i => decide (i = i₀) && b i) := by
    funext i
    have hiff : (recordedPairedPos pairs hlen hb i = recordedPairedPos pairs hlen hb i₀)
        ↔ (i = i₀) := by
      constructor
      · intro h
        exact recordedPairedPos_injective pairs hd hp hlen hb h
      · intro h
        rw [h]
    simp [hiff]
  rw [hfun, booleanListSum_singleton _ i₀ b (List.nodup_finRange _)]
  simp

theorem pairedBlockExtend_unpaired {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (b : Fin (2 * pairs.length) → Bool)
    (j : Fin n) (hj : j ∈ unpairedIndices (List.finRange n) pairs) :
    pairedBlockExtend pairs hlen hb b j = false := by
  unfold pairedBlockExtend
  have hfun : (fun i => decide (recordedPairedPos pairs hlen hb i = j) && b i)
      = (fun _ : Fin (2 * pairs.length) => false) := by
    funext i
    have hne : recordedPairedPos pairs hlen hb i ≠ j := by
      intro he
      exact (recordedPairedPos_not_mem_unpaired pairs hlen hb i) (he ▸ hj)
    simp [hne]
  rw [hfun, booleanListSum_const_false]

/-- The residual kernel is in bijective correspondence with assignments on the paired
block: every assignment on the twice-the-pair-count many paired coordinates is realized
by a unique kernel element. This closes the cardinality parametrization of the kernel,
which the identification at `3171dd6` proved equal to the source polar image. -/
theorem residualKernel_paired_block_bijection {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (b : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    ∃! l, recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
        = zeroVector ∧
      ∀ i, matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
          (recordedPairedPos
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
            hlen hb i) = b i := by
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl0
  have hc : ∀ j ∈ unpairedIndices (List.finRange n)
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2,
      pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
        hlen hb b j = false := by
    intro j hj
    exact pairedBlockExtend_unpaired _ hlen hb b j hj
  obtain ⟨l, hl, huniq⟩ := residualKernel_parametrized_by_pairs p fuel hlen m hsize _ hc
  refine ⟨l, ⟨hl.2, ?_⟩, ?_⟩
  · intro i
    rw [hl.1]
    exact pairedBlockExtend_apply _ hdp.1 hdp.2 hlen hb b i
  · intro l' hl'
    refine residualKernel_determined_by_paired_coordinates p fuel hdegree hlen m hsize l' l
      hl'.1 hl.2 ?_
    intro t htlt
    have hi : t = (⟨(⟨t.val, htlt⟩ : Fin (2 * (polarEliminate (phasePolar p) fuel
        (List.finRange n) identityMatrix).2.2.length)).val, by
          have := t.isLt; omega⟩ : Fin n) := by
      apply Fin.ext
      rfl
    rw [hi]
    have hleft := hl'.2 ⟨t.val, htlt⟩
    have hright : matrixApply (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
        (recordedPairedPos
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
          hlen hb ⟨t.val, htlt⟩) = b ⟨t.val, htlt⟩ := by
      rw [hl.1]
      exact pairedBlockExtend_apply _ hdp.1 hdp.2 hlen hb b _
    exact hleft.trans hright.symm

theorem recordedPairedPos_eq_recordedCoordinateAt {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hb : 2 * pairs.length ≤ n) (t : Fin n) (htlt : t.val < 2 * pairs.length) :
    recordedPairedPos pairs hlen hb ⟨t.val, htlt⟩ = recordedCoordinateAt pairs hlen t := by
  unfold recordedPairedPos
  congr 1

/-- The residual kernel is bijective onto assignments on the paired block. This is the
closed cardinality parametrization in bijection form. -/
theorem residualKernel_pairedBlock_bijective {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Function.Bijective (fun l : {l : BinaryVector n //
        recordedResidualLinearPart
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
          hsize
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
          = zeroVector} =>
      fun i : Fin (2 * (polarEliminate (phasePolar p) fuel
          (List.finRange n) identityMatrix).2.2.length) =>
        matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l.1
          (recordedPairedPos
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
            hlen hb i)) := by
  constructor
  · intro l l' hll
    apply Subtype.ext
    refine residualKernel_determined_by_paired_coordinates p fuel hdegree hlen m hsize
      l.1 l'.1 l.2 l'.2 ?_
    intro t htlt
    have hc := congrFun hll ⟨t.val, htlt⟩
    dsimp only at hc
    rw [recordedPairedPos_eq_recordedCoordinateAt _ hlen hb t htlt] at hc
    exact hc
  · intro b
    obtain ⟨l, hl, _⟩ := residualKernel_paired_block_bijection p fuel hdegree hlen m hsize hb b
    exact ⟨⟨l, hl.1⟩, funext hl.2⟩

/-- Every nonzero exact source Walsh value has magnitude exactly two to the power of the
dimension less the recorded pair count. Since the recorded pair count is half the paired
block size, this is the normalized magnitude of the manuscript's Walsh lemma expressed in
the formalization's own terms. -/
theorem sourceWalshSum_support_natAbs {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hne : sourceWalshSum p l ≠ 0) :
    Int.natAbs (sourceWalshSum p l) = 2 ^ (n -
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) := by
  obtain ⟨hlen, m, hsize, habs⟩ :=
    sourceWalshSum_recorded_interleaved_cast_naturalAbs p l fuel hdegree hbound
  have hnz : Int.natAbs (sourceWalshSum p l) ≠ 0 := by
    intro h
    exact hne (Int.natAbs_eq_zero.mp h)
  rw [habs] at hnz ⊢
  split_ifs at hnz ⊢ with hcond
  · exact absurd rfl hnz
  · congr 1
    omega

/-- The hyperbolic signature is the parity of the products of paired coordinates, so the
sign it controls is a quadratic function of those coordinates. -/
theorem hyperbolicSignature_as_pairProducts (params : List (Bool × Bool)) :
    hyperbolicSignature params
      = (params.map (fun ab => ab.1 && ab.2)).foldr Bool.xor false := by
  induction params with
  | nil => rfl
  | cons ab rest ih => simp [hyperbolicSignature, ih]

/-- Exact value of a nonzero exact source Walsh coefficient: a fixed power of two times
a sign controlled by the recorded constant and the hyperbolic signature of the paired
coordinates. With the previous lemma that signature is the parity of products of paired
coordinates, so the sign is a quadratic function of coordinates on the support. -/
theorem sourceWalshSum_support_value {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hne : sourceWalshSum p l ≠ 0) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    ∃ hlen : (recordedCoordinateOrder pairs).length = n,
      ∃ m, ∃ hsize : n = (pairs.length + pairs.length) + m,
        let f := recordedCoordinateAt pairs hlen
        let r := fun x => evalPhase (recordedPairPhase pairs) x
        let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
        let a := fun i => normalizedDifference
          (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
        let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
        let q := binaryVectorCast hsize (coordinateReindex f t)
        let canonical := coordinateReindex
          (@interleavedIndexFromCanonical pairs.length m) q
        let qs := vectorPairAssignment (canonicalLeft canonical) (canonicalRight canonical)
        sourceWalshSum p l =
          (2 : Int) ^ (n - pairs.length) * integerWalshSign
            (Bool.xor c (hyperbolicSignature
              (pairCoefficientsXor (List.replicate pairs.length (false, false)) qs))) := by
  obtain ⟨hlen, m, hsize, hclosed⟩ :=
    sourceWalshSum_recorded_interleaved_cast_closed p l fuel hdegree hbound
  refine ⟨hlen, m, hsize, ?_⟩
  dsimp only at hclosed ⊢
  rw [hclosed] at hne ⊢
  split_ifs at hne ⊢ with hcond
  · exact absurd rfl hne
  · congr 2
    omega

/-- Executable inverse of an invertible binary matrix action, computed by binary
elimination: run the CNOT sequence of the matrix's Gaussian row program. -/
def gaussianInverseApply {n : Nat} (J : BinaryMatrix n) (y : BinaryVector n) : BinaryVector n :=
  match gaussianRowProgram J with
  | some ops => runCNOTs (rowProgramCNOTs ops) y
  | none => y

/-- Binary elimination computes a preimage: the executable inverse is a right inverse of
an injective matrix action. -/
theorem gaussianInverseApply_forward {n : Nat} (J : BinaryMatrix n)
    (hinj : Function.Injective (matrixApply J)) (y : BinaryVector n) :
    matrixApply J (gaussianInverseApply J y) = y := by
  obtain ⟨ops, hops⟩ := gaussianRowProgram_exists_of_injective J hinj
  simp only [gaussianInverseApply, hops]
  exact matrixApply_inverse_forward J ops hops y

/-- The executable inverse applies to the transpose of the polar-elimination matrix. -/
theorem polarEliminate_transpose_inverseApply {n : Nat}
    (B : BinaryVector n → BinaryVector n → Bool) (fuel : Nat) (indices : List (Fin n))
    (y : BinaryVector n) :
    matrixApply (transposeBinaryMatrix (polarEliminate B fuel indices identityMatrix).1)
      (gaussianInverseApply (transposeBinaryMatrix
        (polarEliminate B fuel indices identityMatrix).1) y) = y := by
  apply gaussianInverseApply_forward
  exact matrixApply_transpose_injective_of_surjective _
    (polarEliminate_surjective B fuel indices)

/-- The residual kernel element realizing a given paired-block target is computed by
binary elimination, with no appeal to choice in its construction. -/
theorem residualKernel_explicit_preimage {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (c : BinaryVector n)
    (hc : ∀ j ∈ unpairedIndices (List.finRange n)
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2, c j = false) :
    matrixApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (gaussianInverseApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) c) = c ∧
      recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (gaussianInverseApply (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) c)
        = zeroVector := by
  have hfwd := polarEliminate_transpose_inverseApply (phasePolar p) fuel (List.finRange n) c
  refine ⟨hfwd, ?_⟩
  rw [residualKernel_iff_transpose_unpaired_zero p fuel hlen m hsize]
  intro j hj
  rw [hfwd]
  exact hc j hj
end SectorSimulation
