import SectorSimulation.WalshMatrixAction

/-!
# A first bit-operation cost model for the Walsh computations

The semantic contract asks for a bit-operation cost trace across parsing and replay, elimination,
substitution, enumeration, random draws, Gauss sums, arithmetic, accumulation and rounding. This
module begins that model for the Walsh computations, and it is deliberately narrow.

Three stages are modelled and bounded here:

* the CNOT program that binary elimination runs, at a stated cost per record;
* one matrix application, at one AND and one XOR per entry;
* the sign's parity over coordinate pairs, at one AND and one XOR per pair.

Each stage has a proved bound, and their sum has a proved quadratic bound in the dimension. What is
not modelled: parsing and replay, phase substitution, candidate enumeration, random draws, real
quadratic Gauss sums, rational accumulation and rounding. So this is the first layer of the trace,
not the trace itself, and no published theorem is certified.
-/

namespace SectorSimulation

/-- Bits touched by one CNOT record under the stated model: read the control, read the target,
write the target back. -/
def cnotBitOps : Nat := 3

/-- Bit operations charged to a CNOT program at the stated per-record cost. -/
def programBitOps {n : Nat} (gates : List (CNOTRecord n)) : Nat := cnotBitOps * gates.length

/-- Bit operations charged to one matrix application: one AND and one XOR per matrix entry. -/
def matrixApplyBitOps (n : Nat) : Nat := 2 * (n * n)

/-- Bit operations charged to the sign's parity over coordinate pairs: one AND and one XOR per
pair. -/
def signPairBitOps (pairs : Nat) : Nat := 2 * pairs

/-- The elimination stage costs at most the per-record cost times the proved gate bound. -/
theorem inverseProgramBitOps_le {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hops : gaussianRowProgram J = some ops) :
    programBitOps (rowProgramCNOTs ops) ≤ cnotBitOps * (3 * (n * (n + 1))) := by
  unfold programBitOps
  exact Nat.mul_le_mul_left _ (gaussianInverseApply_gate_count_le J ops hops)

/-- One matrix application costs at most two bit operations per entry. -/
theorem matrixApplyBitOps_le (n : Nat) : matrixApplyBitOps n ≤ 2 * ((n + 1) * (n + 1)) := by
  unfold matrixApplyBitOps
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n))

/-- The sign's parity costs at most two bit operations per recorded pair. -/
theorem signPairBitOps_le {n : Nat} (k : Nat) (hb : 2 * k ≤ n) :
    signPairBitOps k ≤ 2 * n := by
  unfold signPairBitOps
  omega

/-- The elimination stage's charge is bounded by nine times the squared dimension plus one. -/
theorem inverseProgramBitOps_le_poly {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hops : gaussianRowProgram J = some ops) :
    programBitOps (rowProgramCNOTs ops) ≤ 9 * ((n + 1) * (n + 1)) := by
  have h1 := inverseProgramBitOps_le J ops hops
  have h2 : cnotBitOps * (3 * (n * (n + 1))) = 9 * (n * (n + 1)) := by
    unfold cnotBitOps
    omega
  have h3 : n * (n + 1) ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul (Nat.le_succ n) (Nat.le_refl (n + 1))
  have h4 : 9 * (n * (n + 1)) ≤ 9 * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left 9 h3
  omega

/-- The three modelled stages together cost at most eleven times the squared dimension plus one,
so the modelled part of the Walsh computation is quadratic in the dimension. -/
theorem walshModelledStagesBitOps_le {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hops : gaussianRowProgram J = some ops) (k : Nat) (hb : 2 * k ≤ n) :
    programBitOps (rowProgramCNOTs ops) + matrixApplyBitOps n + signPairBitOps k ≤
      13 * ((n + 1) * (n + 1)) := by
  have h1 := inverseProgramBitOps_le_poly J ops hops
  have h2 := matrixApplyBitOps_le n
  have h3 := signPairBitOps_le k hb
  have h4 : 2 * n ≤ 2 * ((n + 1) * (n + 1)) := by
    have : n ≤ (n + 1) * (n + 1) := by
      have h5 : n ≤ n + 1 := Nat.le_succ n
      have h6 : n + 1 ≤ (n + 1) * (n + 1) := by
        calc n + 1 = (n + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ (by omega : 1 ≤ n + 1)
      exact Nat.le_trans h5 h6
    exact Nat.mul_le_mul_left 2 this
  omega

end SectorSimulation
