import SectorSimulation.WalshCost
import Mathlib.Tactic.Linarith

/-!
# The complete Walsh cost model

`WalshCost` charged three stages. This module extends the model across the stages the semantic
contract lists, with source size, dimensions, precision and confidence as parameters:

* parsing and replay, charged per source bit;
* elimination, charged at the gate bound already proved for the elimination program;
* phase substitution, charged per source monomial per coordinate;
* candidate enumeration, charged over the published candidate count `4 (q+1) 2^(q^2)`;
* random draws, charged over the published draw count `32 4^b (2h+3)`;
* real quadratic Gauss sums, charged per control dimension and precision bit;
* integer and rational arithmetic, accumulation and rounding, charged per source bit or per draw
  at the current working precision.

The total is the sum of those charges, and the elimination stage is proved to dominate the charged
elimination program. What remains open is recorded rather than glossed: the stage charges are
modelling choices stated in the definitions, the substitution, enumeration, draw, Gauss, arithmetic,
accumulation and rounding stages have no proved refinement from an executable algorithm, and the
paper's exact displayed bound is not claimed. No published theorem is certified.
-/

namespace SectorSimulation

/-- The parameters the cost model tracks: source size, dimension, phase count, control cap,
precision bits, confidence and control dimension. -/
structure CostParameters where
  /-- Source size in bits. -/
  sourceBits : Nat
  /-- Circuit dimension. -/
  dimension : Nat
  /-- Number of source monomials. -/
  phaseCount : Nat
  /-- Control cap. -/
  cap : Nat
  /-- Precision bits. -/
  precision : Nat
  /-- Confidence parameter. -/
  confidence : Nat
  /-- Control dimension. -/
  controlDim : Nat

/-- Parsing and replay, one pass over the source bits with constant factor four. -/
def parseBitOps (c : CostParameters) : Nat := 4 * c.sourceBits

/-- Elimination, charged at the proved gate bound of nine times the squared dimension plus one. -/
def eliminationBitOps (c : CostParameters) : Nat :=
  9 * ((c.dimension + 1) * (c.dimension + 1))

/-- Phase substitution, two operations per monomial per coordinate. -/
def substitutionBitOps (c : CostParameters) : Nat := 2 * c.phaseCount * c.dimension

/-- The published candidate count `4 (q+1) 2^(q^2)`. -/
def candidateCount (c : CostParameters) : Nat :=
  4 * (c.cap + 1) * 2 ^ (c.cap * c.cap)

/-- Candidate enumeration, charged per candidate over the cap squared. -/
def enumerationBitOps (c : CostParameters) : Nat := candidateCount c * (c.cap * c.cap)

/-- The published draw count `32 * 4^b * (2h+3)`. -/
def drawCount (c : CostParameters) : Nat :=
  32 * 4 ^ c.precision * (2 * c.confidence + 3)

/-- Random draws, one fair bit each. -/
def drawBitOps (c : CostParameters) : Nat := drawCount c

/-- Real quadratic Gauss sums, four calls per control direction at quadratic precision. -/
def gaussBitOps (c : CostParameters) : Nat :=
  4 * 2 ^ c.controlDim * ((c.precision + 1) * (c.precision + 1))

/-- Integer and rational arithmetic, per source bit at the working precision. -/
def arithmeticBitOps (c : CostParameters) : Nat := c.sourceBits * (c.precision + 1)

/-- Accumulation, per draw at the working precision. -/
def accumulationBitOps (c : CostParameters) : Nat := drawCount c * (c.precision + 1)

/-- Rounding, per draw at the working precision. -/
def roundingBitOps (c : CostParameters) : Nat := drawCount c * (c.precision + 1)

/-- The complete model: the sum of every charged stage. -/
def totalBitOps (c : CostParameters) : Nat :=
  parseBitOps c + eliminationBitOps c + substitutionBitOps c + enumerationBitOps c +
    drawBitOps c + gaussBitOps c + arithmeticBitOps c + accumulationBitOps c +
    roundingBitOps c

/-- The model's total is exactly the sum of its stages. -/
theorem totalBitOps_eq_stages (c : CostParameters) :
    totalBitOps c =
      parseBitOps c + eliminationBitOps c + substitutionBitOps c + enumerationBitOps c +
        drawBitOps c + gaussBitOps c + arithmeticBitOps c + accumulationBitOps c +
        roundingBitOps c := rfl

/-- The charged elimination program is dominated by the model's elimination stage. -/
theorem programBitOps_le_eliminationBitOps {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hops : gaussianRowProgram J = some ops)
    (c : CostParameters) (hc : c.dimension = n) :
    programBitOps (rowProgramCNOTs ops) ≤ eliminationBitOps c := by
  have h := inverseProgramBitOps_le_poly J ops hops
  subst hc
  exact Nat.le_trans h (Nat.le_refl _)

/-! ## The polynomial envelope for the non-exponential stages -/

/-- The combined size the envelope is measured in: source bits, dimension and phase count. -/
def sizeEnvelope (c : CostParameters) : Nat :=
  c.sourceBits + c.dimension + c.phaseCount + 2

/-- The polynomial envelope, scaled by the working precision. -/
def stageEnvelope (c : CostParameters) : Nat :=
  16 * (sizeEnvelope c * sizeEnvelope c) * (c.precision + 1)

/-! A quantity inside sixteen squared envelopes is inside the envelope. -/
theorem le_stageEnvelope_of_le {c : CostParameters} {x : Nat}
    (hx : x ≤ 16 * (sizeEnvelope c * sizeEnvelope c)) :
    x ≤ stageEnvelope c := by
  have hprec : 1 ≤ c.precision + 1 := Nat.succ_le_succ (Nat.zero_le _)
  unfold stageEnvelope
  calc x ≤ 16 * (sizeEnvelope c * sizeEnvelope c) := hx
    _ = 16 * (sizeEnvelope c * sizeEnvelope c) * 1 := (Nat.mul_one _).symm
    _ ≤ 16 * (sizeEnvelope c * sizeEnvelope c) * (c.precision + 1) :=
        Nat.mul_le_mul_left _ hprec

/-- Parsing and replay lie inside the envelope. -/
theorem parseBitOps_le_stageEnvelope (c : CostParameters) :
    parseBitOps c ≤ stageEnvelope c := by
  apply le_stageEnvelope_of_le
  unfold parseBitOps sizeEnvelope
  have hB : c.sourceBits ≤ c.sourceBits + c.dimension + c.phaseCount + 2 := by omega
  nlinarith [Nat.zero_le c.sourceBits, Nat.zero_le c.dimension, Nat.zero_le c.phaseCount]

/-- Elimination lies inside the envelope: the proved gate bound is quadratic in the dimension. -/
theorem eliminationBitOps_le_stageEnvelope (c : CostParameters) :
    eliminationBitOps c ≤ stageEnvelope c := by
  apply le_stageEnvelope_of_le
  unfold eliminationBitOps sizeEnvelope
  have hd : c.dimension + 1 ≤ c.sourceBits + c.dimension + c.phaseCount + 2 := by omega
  have hd2 : (c.dimension + 1) * (c.dimension + 1) ≤
      (c.sourceBits + c.dimension + c.phaseCount + 2) *
        (c.sourceBits + c.dimension + c.phaseCount + 2) := Nat.mul_le_mul hd hd
  nlinarith [Nat.zero_le (c.sourceBits + c.dimension + c.phaseCount + 2)]

/-- Phase substitution lies inside the envelope. -/
theorem substitutionBitOps_le_stageEnvelope (c : CostParameters) :
    substitutionBitOps c ≤ stageEnvelope c := by
  apply le_stageEnvelope_of_le
  unfold substitutionBitOps sizeEnvelope
  have hp : c.phaseCount ≤ c.sourceBits + c.dimension + c.phaseCount + 2 := by omega
  have hd : c.dimension ≤ c.sourceBits + c.dimension + c.phaseCount + 2 := by omega
  have hpd : c.phaseCount * c.dimension ≤
      (c.sourceBits + c.dimension + c.phaseCount + 2) *
        (c.sourceBits + c.dimension + c.phaseCount + 2) := Nat.mul_le_mul hp hd
  nlinarith [Nat.zero_le (c.sourceBits + c.dimension + c.phaseCount + 2)]

/-- Integer and rational arithmetic lies inside the envelope. -/
theorem arithmeticBitOps_le_stageEnvelope (c : CostParameters) :
    arithmeticBitOps c ≤ stageEnvelope c := by
  unfold arithmeticBitOps stageEnvelope sizeEnvelope
  have hB : c.sourceBits ≤ c.sourceBits + c.dimension + c.phaseCount + 2 := by omega
  have h1 : c.sourceBits ≤ 16 * ((c.sourceBits + c.dimension + c.phaseCount + 2) *
      (c.sourceBits + c.dimension + c.phaseCount + 2)) := by
    nlinarith [Nat.zero_le (c.sourceBits + c.dimension + c.phaseCount + 2)]
  calc c.sourceBits * (c.precision + 1)
      ≤ (16 * ((c.sourceBits + c.dimension + c.phaseCount + 2) *
          (c.sourceBits + c.dimension + c.phaseCount + 2))) * (c.precision + 1) :=
        Nat.mul_le_mul_right _ h1
    _ = 16 * ((c.sourceBits + c.dimension + c.phaseCount + 2) *
          (c.sourceBits + c.dimension + c.phaseCount + 2)) * (c.precision + 1) := by
        rw [Nat.mul_assoc]

/-- The non-exponential stages together lie inside four envelopes: a polynomial in the combined
source size and dimension, scaled by the working precision. -/
theorem sourceStagesBitOps_le (c : CostParameters) :
    parseBitOps c + eliminationBitOps c + substitutionBitOps c + arithmeticBitOps c ≤
      4 * stageEnvelope c := by
  have h1 := parseBitOps_le_stageEnvelope c
  have h2 := eliminationBitOps_le_stageEnvelope c
  have h3 := substitutionBitOps_le_stageEnvelope c
  have h4 := arithmeticBitOps_le_stageEnvelope c
  omega

/-- The complete model is the four enveloped stages plus the three exponential stages. -/
theorem totalBitOps_le (c : CostParameters) :
    totalBitOps c ≤
      4 * stageEnvelope c + enumerationBitOps c + drawBitOps c + gaussBitOps c +
        accumulationBitOps c + roundingBitOps c := by
  have h := sourceStagesBitOps_le c
  unfold totalBitOps
  omega

end SectorSimulation
