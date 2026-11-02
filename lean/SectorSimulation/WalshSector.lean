import SectorSimulation.WalshMatrix
import SectorSimulation.MatrixPairing
import SectorSimulation.HadamardWalshCoefficient
import SectorSimulation.DyadicQuotient

/-!
# The sector state `psi_a`

The paper's sector construction has been absent from this development: no sector state, no Clifford
observable and no `psi` existed anywhere. This module defines the sector state in exact amplitudes,

`psi_a(y) = 2^(-r/2) * (-1)^( f0(R a + D y) + (J beta) . (R a + D y) )`,

from objects that are already proved here: the support coordinates `D y` and the right inverse
`R a` that together give the support point, the matrix pairing character `matrixPairingParity`, the
first-phase evaluator `evalPhase`, and the exact dyadic whose value is `2^(-r/2)`.

Scope of this module: the definition only. No theorem is claimed, and the correspondence between
this `psi_a` and the paper's own object is deliberately deferred to the sector proposition: the
formalization measures the rank and the basis by the computed polar elimination, so identifying
them with the paper's `r`, `D`, `C` and `R` needs the rank identification in the statement's
hypotheses (`hbound : n ≤ fuel`) together with the pairing symmetry and invertibility and the cubic
phases. That identification is not asserted here.
-/

namespace SectorSimulation

/-- The paper's sector state at sector label `a` and coordinate tuple `y`, in exact amplitudes.

The support point is `R a + D y`, where `R` is the computed right inverse of the annihilator and `D`
is the computed basis matrix; the sign is the first phase evaluated there, xored with the matrix
pairing of the input character against it; the normalization is the exact dyadic `2^(-r/2)`, which
is `2^(-pairCount)` because the rank is twice the recorded pair count. -/
noncomputable def sectorState {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m)
    (y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) : ExactAmplitude :=
  let pc := (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length
  let point : BinaryVector n := vectorXor
    (residualRightInverse m q fuel hlen hsize a)
    (matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb) (extendCoordinates q fuel y))
  exactMul (exactOfDyadic ⟨cycloOne, pc⟩)
    (exactSigned (Bool.xor (evalPhase f0 point) (matrixPairingParity J point beta)) exactOne)

/-- Unfolding lemma for `sectorState`: the state is the dyadic normalization times the sign on the
support point. Recorded so later sector statements can rewrite without unfolding the definition. -/
theorem sectorState_eq {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m)
    (y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    sectorState q f0 J beta fuel hdegree hlen m hsize hb a y =
      exactMul (exactOfDyadic ⟨cycloOne,
          (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length⟩)
        (exactSigned (Bool.xor
          (evalPhase f0 (vectorXor
            (residualRightInverse m q fuel hlen hsize a)
            (matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb)
              (extendCoordinates q fuel y))))
          (matrixPairingParity J
            (vectorXor
              (residualRightInverse m q fuel hlen hsize a)
              (matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb)
                (extendCoordinates q fuel y)))
            beta)) exactOne) := rfl

end SectorSimulation
