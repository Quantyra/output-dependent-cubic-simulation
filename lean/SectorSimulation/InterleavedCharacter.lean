import SectorSimulation.RecordedInterleavedPhase

namespace SectorSimulation

theorem booleanListSum_perm {α : Type} (xs ys : List α) (h : xs.Perm ys) (f : α → Bool) :
    booleanListSum xs f = booleanListSum ys f := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp only [booleanListSum, List.foldr_cons]
      exact congrArg (Bool.xor (f a)) (by simpa only [booleanListSum] using ih)
  | swap a b xs =>
      simp only [booleanListSum, List.foldr_cons]
      cases f a <;> cases f b <;>
        cases hrest : List.foldr (fun x acc => Bool.xor (f x) acc) false xs <;> rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem booleanListSum_map {α β : Type} (xs : List α) (g : α → β) (f : β → Bool) :
    booleanListSum xs (fun x => f (g x)) = booleanListSum (xs.map g) f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, booleanListSum, List.foldr_cons]
      exact congrArg (Bool.xor (f (g x))) (by simpa only [booleanListSum] using ih)

theorem coordinateMap_finRange_perm {n : Nat} (g : Fin n → Fin n)
    (hinj : Function.Injective g) (hsurj : ∀ x, ∃ i, g i = x) :
    ((List.finRange n).map g).Perm (List.finRange n) := by
  have hnd : ((List.finRange n).map g).Nodup :=
    List.Pairwise.map _ (fun _ _ h he => h (hinj he)) (List.nodup_finRange n)
  have hm : ∀ z, z ∈ (List.finRange n).map g ↔ z ∈ List.finRange n := by
    intro z
    constructor
    · intro _
      exact List.mem_finRange z
    · intro hz
      obtain ⟨i, hi⟩ := hsurj z
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, hi⟩
  apply List.perm_iff_count.mpr
  intro z
  rw [hnd.count, (List.nodup_finRange n).count]
  simp [hm z]

/-- A Walsh character moves through the inverse recorded-coordinate map by
reindexing its coefficient vector through the forward coordinate map. -/
theorem walshWireParity_coordinateReindex {n : Nat} (f g : Fin n → Fin n)
    (hfg : ∀ i, f (g i) = i) (hgf : ∀ i, g (f i) = i)
    (t y : BinaryVector n) :
    walshWireParity (List.finRange n) t (coordinateReindex g y) =
      walshWireParity (List.finRange n) (coordinateReindex f t) y := by
  rw [walshWireParity_as_sum, walshWireParity_as_sum]
  have hginj : Function.Injective g := by
    intro i j hij
    have h := congrArg f hij
    simpa [hfg i, hfg j] using h
  have hgsurj : ∀ x, ∃ i, g i = x := by
    intro x
    exact ⟨f x, hgf x⟩
  have hperm := coordinateMap_finRange_perm g hginj hgsurj
  have hterm : (fun i => t i && y (g i)) =
      (fun i => t (f (g i)) && y (g i)) := by
    funext i
    rw [hfg i]
  calc
    booleanListSum (List.finRange n) (fun i => t i && y (g i)) =
        booleanListSum (List.finRange n) (fun i => t (f (g i)) && y (g i)) := by rw [hterm]
    _ = booleanListSum ((List.finRange n).map g) (fun j => t (f j) && y j) :=
      booleanListSum_map (List.finRange n) g (fun j => t (f j) && y j)
    _ = booleanListSum (List.finRange n) (fun j => t (f j) && y j) :=
      booleanListSum_perm _ _ hperm _

theorem recordedPairInterleavedWalshSum {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n)
    (hinj : Function.Injective (recordedCoordinateAt pairs hlen))
    (hsurj : ∀ x, ∃ i, recordedCoordinateAt pairs hlen i = x)
    (c : Bool) (t : BinaryVector n) :
    ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor c (Bool.xor
        (evalPhase (recordedPairPhase pairs)
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y))
        (walshWireParity (List.finRange n) t
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y)))))).sum =
    ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor
        (pairPhaseEval (List.replicate pairs.length (false, false))
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
              omega⟩)) c)
        (walshWireParity (List.finRange n) (coordinateReindex (recordedCoordinateAt pairs hlen) t) y)))).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  apply congrArg integerWalshSign
  calc
    _ = Bool.xor
        (Bool.xor c (evalPhase (recordedPairPhase pairs)
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y)))
        (walshWireParity (List.finRange n) t
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y)) :=
      (Bool.xor_assoc _ _ _).symm
    _ = Bool.xor
        (pairPhaseEval (List.replicate pairs.length (false, false))
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
              omega⟩)) c)
        (walshWireParity (List.finRange n) t
          (coordinateReindex (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj) y)) := by
      rw [recordedPairPhase_interleaved pairs hlen hinj hsurj y c]
    _ = Bool.xor
        (pairPhaseEval (List.replicate pairs.length (false, false))
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
              omega⟩)) c)
        (walshWireParity (List.finRange n) (coordinateReindex (recordedCoordinateAt pairs hlen) t) y) := by
      rw [walshWireParity_coordinateReindex
        (recordedCoordinateAt pairs hlen)
        (coordinateInverse (recordedCoordinateAt pairs hlen) hsurj)
        (coordinateInverse_right (recordedCoordinateAt pairs hlen) hsurj)
        (coordinateInverse_left (recordedCoordinateAt pairs hlen) hinj hsurj) t y]

theorem sourceWalshSum_recorded_interleaved {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (fuel : Nat) (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix
    let pairs := out.2.2
    ∃ hlen : (recordedCoordinateOrder pairs).length = n,
      let f := recordedCoordinateAt pairs hlen
      let r := fun x => evalPhase (recordedPairPhase pairs) x
      let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
      let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply out.1 y)) r (coordinateUnit i)
      let t := binaryShift a (matrixApply (transposeBinaryMatrix out.1) l)
      sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
        (Bool.xor
          (pairPhaseEval (List.replicate pairs.length (false, false))
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
                omega⟩)) c)
          (walshWireParity (List.finRange n) (coordinateReindex f t) y)))).sum := by
  dsimp only
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl : ∀ x, phasePolar p x x = false := by
    intro x
    rw [hpolar]
    exact halt x
  have hd := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n) identityMatrix hl
  let pairs := (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
  have hlen : (recordedCoordinateOrder pairs).length = n := by
    simpa using (recordedCoordinateOrder_perm pairs hd.1 hd.2).length_eq
  have hb := recordedCoordinateAt_bijective pairs hd.1 hd.2
  refine ⟨hlen, ?_⟩
  dsimp only
  let f := recordedCoordinateAt pairs hlen
  let inv := coordinateInverse f hb.2
  let r := fun x => evalPhase (recordedPairPhase pairs) x
  let c := Bool.xor (evalPhase p (fun _ => false)) (r (fun _ => false))
  let a := fun i => normalizedDifference (fun y => evalPhase p (matrixApply
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y)) r (coordinateUnit i)
  let t := binaryShift a (matrixApply (transposeBinaryMatrix
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l)
  have hbase := sourceWalshSum_recorded_inverse_reindex p l fuel hdegree hbound hd.1 hd.2
  dsimp only at hbase
  rw [hbase]
  have hphase (y : BinaryVector n) := recordedPairPhase_interleaved pairs hlen hb.1 hb.2 y c
  have hchar (y : BinaryVector n) := walshWireParity_coordinateReindex f inv
    (coordinateInverse_right f hb.2) (coordinateInverse_left f hb.1 hb.2) t y
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  apply congrArg integerWalshSign
  calc
    _ = Bool.xor (Bool.xor c (evalPhase (recordedPairPhase pairs) (coordinateReindex inv y)))
        (walshWireParity (List.finRange n) t (coordinateReindex inv y)) := (Bool.xor_assoc _ _ _).symm
    _ = Bool.xor
        (pairPhaseEval (List.replicate pairs.length (false, false))
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
              omega⟩)) c)
        (walshWireParity (List.finRange n) t (coordinateReindex inv y)) := by
      rw [hphase y]
    _ = Bool.xor
        (pairPhaseEval (List.replicate pairs.length (false, false))
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
              omega⟩)) c)
        (walshWireParity (List.finRange n) (coordinateReindex f t) y) := by
      rw [hchar y]

end SectorSimulation
