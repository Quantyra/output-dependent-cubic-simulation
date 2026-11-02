import SectorSimulation.WalshSector
import SectorSimulation.ComplexSemantics
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The sector state is a unit vector

The first statement proved about the sector state: summed over its coordinate index, the squared
modulus of the exact amplitude is one. With `pc` the recorded pair count and `r = 2 * pc` the sector
rank, the state is `2^(-pc)` times a sign, so each squared modulus is `2^(-2 * pc)` and there are
`2^(2 * pc)` coordinate tuples.

Scope: this is a normalization statement about the constructed state. It is phase independent --- the
sign cancels in the modulus --- so it certifies nothing about the phase, and it says nothing about the
paper's own `psi_a`, whose identification with this object is the sector proposition's job and needs
the rank identification with `hbound : n <= fuel`, the pairing hypotheses and the cubic phases. It
also does not assert that `y |-> R a + D y` is injective, so the indexed amplitude vector is not yet
identified with a vector in a physical sector basis.
-/

namespace SectorSimulation

open scoped BigOperators

/-- The exact dyadic `2^(-k)`, read in `ℂ`, is `1 / 2^k`. -/
theorem exactComplex_dyadicPow (k : Nat) :
    exactComplex (exactOfDyadic ⟨cycloOne, k⟩) = (1 : ℂ) / (2 : ℂ) ^ k := by
  change dyadicInterpret ⟨cycloOne, k⟩ = (1 : ℂ) / (2 : ℂ) ^ k
  simp [dyadicInterpret, cycloInterpret, cycloOne]

/-- A sign applied to one has unit squared modulus. -/
theorem normSq_complexSigned_one (b : Bool) :
    Complex.normSq (complexSigned b (1 : ℂ)) = 1 := by
  cases b <;> simp [complexSigned, Complex.normSq]

/-- The exact sign `±1` has unit squared modulus. -/
theorem normSq_exactComplex_signed_one (b : Bool) :
    Complex.normSq (exactComplex (exactSigned b exactOne)) = 1 := by
  rw [exactComplex_signed, exactComplex_one]
  exact normSq_complexSigned_one b

/-- Every sector amplitude has squared modulus `2^(-2 * pc)`, independently of the sign. -/
theorem sectorState_normSq {n : Nat}
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
    Complex.normSq (exactComplex (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y))
      = (1 / (2 : ℝ) ^
          ((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length)) ^ 2 := by
  rw [sectorState_eq, exactComplex_mul, Complex.normSq_mul,
    normSq_exactComplex_signed_one, mul_one, exactComplex_dyadicPow]
  have hcast : (1 : ℂ) / (2 : ℂ) ^
        ((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length)
      = (((1 / (2 : ℝ) ^
        ((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.normSq_ofReal]
  ring

/-- The sector state is a unit vector: summed over the coordinate index, the squared moduli total one.

This is the paper's normalization clause for the sector state, proved about the constructed state at
the paper's `2^(-r/2)` normalization with `r = 2 * pc`. It is not the correspondence with the paper's
`psi_a` and does not identify the index with a physical sector basis. -/
theorem sectorState_unit_norm {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) :
    (∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool),
      Complex.normSq (exactComplex (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y))) = 1 := by
  classical
  have h1 :
      (∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool),
        Complex.normSq (exactComplex (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y))) =
      (∑ _y : (Fin (2 * (polarEliminate (phasePolar q) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool),
        (1 / (2 : ℝ) ^
          ((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length)) ^ 2) :=
    Finset.sum_congr rfl (fun y _ => sectorState_normSq q f0 J beta fuel hdegree hlen m hsize hb a y)
  rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool)
      = 2 ^ (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard]
  have hcastN : ((2 ^ (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) : Nat) : ℝ)
      = (2 : ℝ) ^ (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) := by
    push_cast
    ring
  rw [hcastN]
  have hpow : ((2 : ℝ) ^ ((polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length)) ^ 2
      = (2 : ℝ) ^ (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) := by
    rw [pow_two, ← pow_add, Nat.two_mul]
  rw [← hpow, ← mul_pow]
  have hne : (2 : ℝ) ^ ((polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_one_div_cancel hne, one_pow]

end SectorSimulation
