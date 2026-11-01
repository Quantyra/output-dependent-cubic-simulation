import SectorSimulation.WalshBasis

/-!
# The support sign as a function of the coordinate tuple

The Walsh lemma states the sign on the support as a quadratic function of support coordinates.
`WalshBasis` supplies the coordinate system: a kernel element is exactly the paired-block
extension of its coordinates on the transformed character. This module composes that with the
linearity of the canonical coordinate map to state the sign on a support character of the form
`l0 xor kernelCoordinateElement y` as the recorded constant xored with the parity over coordinate
pairs of `(alpha_i xor y(2i)) && (beta_i xor y(2i+1))`, where `alpha` and `beta` are the canonical
coordinates of the affine base.

It does not define the manuscript matrix `D` itself, does not supply a bit-operation cost trace,
and certifies no published theorem.
-/

namespace SectorSimulation

open Classical

/-- The derivative shift is the pointwise XOR with the shift vector. -/
theorem binaryShift_eq_vectorXor {n : Nat} (a z : BinaryVector n) :
    binaryShift a z = vectorXor z a := rfl

/-- Pointwise XOR is associative. -/
theorem vectorXor_assoc {n : Nat} (a b c : BinaryVector n) :
    vectorXor (vectorXor a b) c = vectorXor a (vectorXor b c) := by
  funext i
  simp [vectorXor]

/-- Pointwise XOR is commutative. -/
theorem vectorXor_comm {n : Nat} (a b : BinaryVector n) :
    vectorXor a b = vectorXor b a := by
  funext i
  simp [vectorXor, Bool.xor_comm]

/-- A Boolean list sum respects pointwise equality of its summand. -/
theorem booleanListSum_congr {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : booleanListSum xs f = booleanListSum xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show Bool.xor (f x) (booleanListSum rest f) = Bool.xor (g x) (booleanListSum rest g)
      rw [h x (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The affine base of the sign computation: the normalized difference vector applied to the
transformed base character. -/
noncomputable def supportSignBase {n : Nat} (m : Nat) (p : PhaseANF n)
    (pairs : List (Fin n × Fin n))
    (J : BinaryMatrix n) (l₀ : BinaryVector n) : BinaryVector n :=
  binaryShift (fun i => normalizedDifference (fun y => evalPhase p (matrixApply J y))
    (fun x => evalPhase (recordedPairPhase pairs) x) (coordinateUnit i))
    (matrixApply (transposeBinaryMatrix J) l₀)

/-- The support sign is the recorded constant xored with the parity over coordinate pairs of the
products of the affine coordinate functions: the manuscript's quadratic sign, as a function of
the `r`-tuple. -/
theorem sourceWalshSupportSign_coordinates {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool) (l₀ : BinaryVector n) :
    sourceWalshSupportSign p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
        (vectorXor l₀ (kernelCoordinateElement p fuel hdegree hlen m hsize hb y)) =
      Bool.xor
        (Bool.xor (evalPhase p (fun _ => false))
          (evalPhase (recordedPairPhase (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) (fun _ => false)))
        (booleanListSum (List.finRange (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) (fun i =>
          Bool.xor
            (canonicalLeft ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
              (supportSignBase m p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 l₀)) i)
            (y ⟨2 * i.val, by have := i.isLt; omega⟩) &&
          Bool.xor
            (canonicalRight ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
              (supportSignBase m p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 l₀)) i)
            (y ⟨2 * i.val + 1, by have := i.isLt; omega⟩))) := by
  classical
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n)
    identityMatrix hl0
  -- the canonical coordinates of the shifted character, split into base and coordinates
  have hinner : (recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
      (binaryShift (fun i => normalizedDifference (fun y => evalPhase p (matrixApply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y))
  (fun x => evalPhase (recordedPairPhase (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x) (coordinateUnit i))
        (matrixApply (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
          (vectorXor l₀ (kernelCoordinateElement p fuel hdegree hlen m hsize hb y)))) =
      vectorXor
        ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize) (supportSignBase m p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 l₀))
        ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize) (pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y)) := by
    rw [binaryShift_eq_vectorXor, matrixApply_xor,
      transpose_kernelCoordinateElement p fuel hdegree hlen m hsize hb y]
    rw [vectorXor_assoc, vectorXor_comm (pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y)
      (fun i => normalizedDifference (fun y => evalPhase p (matrixApply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y))
  (fun x => evalPhase (recordedPairPhase (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x) (coordinateUnit i)), ← vectorXor_assoc]
    rw [recordedCanonicalCoordinates_vectorXor, recordedCanonicalCoordinates_vectorXor,
      ← recordedCanonicalCoordinates_vectorXor, ← binaryShift_eq_vectorXor]
    rfl
  rw [sourceWalshSupportSign_as_quadratic (k := (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize rfl (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
    (vectorXor l₀ (kernelCoordinateElement p fuel hdegree hlen m hsize hb y))]
  congr 1
  apply booleanListSum_congr
  intro i _
  have hleft : canonicalLeft ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
        (binaryShift (fun i => normalizedDifference (fun y => evalPhase p (matrixApply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y))
  (fun x => evalPhase (recordedPairPhase (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x) (coordinateUnit i))
          (matrixApply (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
            (vectorXor l₀ (kernelCoordinateElement p fuel hdegree hlen m hsize hb y))))) i =
      Bool.xor (canonicalLeft ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
        (supportSignBase m p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 l₀)) i)
        (y ⟨2 * i.val, by have := i.isLt; omega⟩) := by
    rw [hinner, canonicalLeft_vectorXor]
    have hl := canonicalLeft_recordedCanonicalCoordinates_pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hdp.1 hdp.2 hlen hsize rfl hb y i
    exact congrArg (fun b => Bool.xor _ b) hl
  have hright : canonicalRight ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
        (binaryShift (fun i => normalizedDifference (fun y => evalPhase p (matrixApply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 y))
  (fun x => evalPhase (recordedPairPhase (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x) (coordinateUnit i))
          (matrixApply (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
            (vectorXor l₀ (kernelCoordinateElement p fuel hdegree hlen m hsize hb y))))) i =
      Bool.xor (canonicalRight ((recordedCanonicalCoordinates (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize)
        (supportSignBase m p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 l₀)) i)
        (y ⟨2 * i.val + 1, by have := i.isLt; omega⟩) := by
    rw [hinner, canonicalRight_vectorXor]
    have hr := canonicalRight_recordedCanonicalCoordinates_pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hdp.1 hdp.2 hlen hsize rfl hb y i
    exact congrArg (fun b => Bool.xor _ b) hr
  exact congrArg₂ (fun a b => a && b) hleft hright

end SectorSimulation
