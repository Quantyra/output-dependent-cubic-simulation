import SectorSimulation.HadamardKernel
namespace SectorSimulation

theorem dyadicAdd_assoc (a b c : DyadicCyclo) :
    dyadicAdd (dyadicAdd a b) c = dyadicAdd a (dyadicAdd b c) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases c with | mk cn ce =>
        cases an; cases bn; cases cn
        simp only [dyadicAdd, cycloAdd, cycloScale, DyadicCyclo.mk.injEq, Cyclo8.mk.injEq,
          Int.pow_add, Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Nat.add_assoc, Int.add_assoc]


theorem exactAdd_assoc (a b c : ExactAmplitude) :
    exactAdd (exactAdd a b) c = exactAdd a (exactAdd b c) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change exactOfDyadic (dyadicAdd (dyadicAdd a b) c) = exactOfDyadic (dyadicAdd a (dyadicAdd b c))
        rw [dyadicAdd_assoc]

theorem exactSub_eq_add_neg (a b : ExactAmplitude) : exactSub a b = exactAdd a (exactNeg b) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change exactOfDyadic (dyadicSubtract a b) = exactOfDyadic (dyadicAdd a (dyadicNeg b))
      rw [dyadicSubtract_eq_add_neg]

theorem exactMul_assoc (a b c : ExactAmplitude) :
    exactMul (exactMul a b) c = exactMul a (exactMul b c) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change exactOfDyadic (dyadicMultiply (dyadicMultiply a b) c) =
          exactOfDyadic (dyadicMultiply a (dyadicMultiply b c))
        congr 1
        cases a; cases b; cases c
        simp [dyadicMultiply, cyclo_mul_assoc, Nat.add_assoc]


end SectorSimulation
