import SectorSimulation.WalshCoordinates

/-!
# The manuscript's basis columns, annihilator and right inverse for the polar image

`WalshCoordinates` parametrizes the exact source Walsh support by rank many coordinates through
the recorded paired block. This module presents that parametrization in the shape the manuscript
uses: a family of basis columns for the polar image, the annihilator map `C` whose kernel is that
image, and a computed right inverse `R` of `C`.

Concretely, `kernelCoordinateElement` is the coordinate element, `supportBasisColumn` is the
`i`-th basis column, `supportBasisColumns_span_polarImage` says that the coordinate elements are
exactly the kernel of `C`, and `residualRightInverse_spec` says that `R` inverts `C`. It does not
express the quadratic sign in these coordinates and certifies no published theorem.
-/

namespace SectorSimulation

open Classical

/-- The residual-kernel element with prescribed recorded paired-block coordinates. -/
noncomputable def kernelCoordinateElement {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) : BinaryVector n :=
  Classical.choose (residualKernel_paired_block_bijection p fuel hdegree hlen m hsize hb y).exists

/-! The specification of the coordinate element: it lies in the kernel and has the prescribed
recorded paired-block coordinates. -/
theorem kernelCoordinateElement_spec {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    (recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (kernelCoordinateElement p fuel hdegree hlen m hsize hb y) = zeroVector) ∧
      (∀ i : Fin (2 * (polarEliminate (phasePolar p) fuel
          (List.finRange n) identityMatrix).2.2.length),
        matrixApply
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
          (kernelCoordinateElement p fuel hdegree hlen m hsize hb y)
          (recordedPairedPos
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb i) = y i) :=
  Classical.choose_spec
    (residualKernel_paired_block_bijection p fuel hdegree hlen m hsize hb y).exists

/-- The coordinate element lies in the polar image, i.e. in the kernel of the annihilator. -/
theorem kernelCoordinateElement_mem {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (kernelCoordinateElement p fuel hdegree hlen m hsize hb y) = zeroVector :=
  (kernelCoordinateElement_spec p fuel hdegree hlen m hsize hb y).1

/-- The coordinate element has exactly the prescribed recorded paired-block coordinates. -/
theorem kernelCoordinateElement_coordinates {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool)
    (i : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length)) :
    matrixApply
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (kernelCoordinateElement p fuel hdegree hlen m hsize hb y)
      (recordedPairedPos
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb i) = y i :=
  (kernelCoordinateElement_spec p fuel hdegree hlen m hsize hb y).2 i

/-- A kernel element is determined, on the transformed character, by its recorded paired-block
coordinates: the transformed character is exactly the paired-block extension of those
coordinates. -/
theorem transpose_eq_pairedBlockExtend_of_kernel {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (l : BinaryVector n)
    (hl : recordedResidualLinearPart
      (recordedCoordinateAt
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
      hsize
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool)
    (hcoord : ∀ i : Fin (2 * (polarEliminate (phasePolar p) fuel
        (List.finRange n) identityMatrix).2.2.length),
      matrixApply
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
        (recordedPairedPos
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb i) = y i) :
    matrixApply
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l =
      pairedBlockExtend
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y := by
  classical
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n)
    identityMatrix hl0
  funext j
  obtain (⟨tr, hlt, ht⟩ | hunp) :=
    recordedIndex_paired_or_unpaired
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
      hdp.1 hdp.2 hlen hsize j
  · rw [← ht, ← recordedPairedPos_eq_recordedCoordinateAt
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb tr hlt]
    rw [hcoord ⟨tr.val, hlt⟩, pairedBlockExtend_apply
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
      hdp.1 hdp.2 hlen hb y ⟨tr.val, hlt⟩]
  · rw [pairedBlockExtend_unpaired
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y j hunp]
    exact (residualKernel_iff_transpose_unpaired_zero p fuel hlen m hsize l).mp hl j hunp

/-- The transformed coordinate element is the paired-block extension of its coordinates. -/
theorem transpose_kernelCoordinateElement {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    matrixApply
      (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (kernelCoordinateElement p fuel hdegree hlen m hsize hb y) =
      pairedBlockExtend
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y :=
  transpose_eq_pairedBlockExtend_of_kernel p fuel hdegree hlen m hsize hb _
    (kernelCoordinateElement_mem p fuel hdegree hlen m hsize hb y) y
    (kernelCoordinateElement_coordinates p fuel hdegree hlen m hsize hb y)

/-- The `i`-th basis column of the polar image: the coordinate element of the unit tuple. -/
noncomputable def supportBasisColumn {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (i : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length)) : BinaryVector n :=
  kernelCoordinateElement p fuel hdegree hlen m hsize hb (fun j => decide (j = i))

/-- The coordinate elements are exactly the polar image, so the basis columns span it: the
manuscript's `im(D)` is the kernel of its annihilator `C`. -/
theorem supportBasisColumns_span_polarImage {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (l : BinaryVector n) :
    recordedResidualLinearPart
        (recordedCoordinateAt
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
        hsize
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector ↔
      ∃ y : Fin (2 * (polarEliminate (phasePolar p) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool,
        kernelCoordinateElement p fuel hdegree hlen m hsize hb y = l := by
  classical
  constructor
  · intro hl
    let y : Fin (2 * (polarEliminate (phasePolar p) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool := fun i =>
      matrixApply
        (transposeBinaryMatrix
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l
        (recordedPairedPos
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb i)
    refine ⟨y, ?_⟩
    have hinj := matrixApply_transpose_injective_of_surjective
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
      (polarEliminate_surjective (phasePolar p) fuel (List.finRange n))
    apply hinj
    rw [transpose_kernelCoordinateElement p fuel hdegree hlen m hsize hb y,
      transpose_eq_pairedBlockExtend_of_kernel p fuel hdegree hlen m hsize hb l hl y (fun i => rfl)]
  · rintro ⟨y, rfl⟩
    exact kernelCoordinateElement_mem p fuel hdegree hlen m hsize hb y

/-- The annihilator map `C`: the residual linear part of the transformed character. -/
noncomputable def residualAnnihilator {n : Nat} (m : Nat)
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (l : BinaryVector n) : BinaryVector m :=
  recordedResidualLinearPart
    (recordedCoordinateAt
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
    hsize
    (transposeBinaryMatrix
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l

/-- The computed right inverse `R` of the annihilator map. -/
noncomputable def residualRightInverse {n : Nat} (m : Nat)
    (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (w : BinaryVector m) : BinaryVector n :=
  recordedResidualPreimage
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize
    (transposeBinaryMatrix
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) w

/-- `R` really is a right inverse of the annihilator map `C`. -/
theorem residualRightInverse_spec {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (w : BinaryVector m) :
    residualAnnihilator m p fuel hlen hsize (residualRightInverse m p fuel hlen hsize w) = w := by
  classical
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n)
    identityMatrix hl0
  exact recordedResidualPreimage_correct
    (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
    hdp.1 hdp.2 hlen hsize _
    (matrixApply_transpose_injective_of_surjective
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
      (polarEliminate_surjective (phasePolar p) fuel (List.finRange n))) w

end SectorSimulation
