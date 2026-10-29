import SectorSimulation.ExactWalshAlgebra
namespace SectorSimulation

theorem cycloScale_add (k : Int) (a b : Cyclo8) :
    cycloScale k (cycloAdd a b) = cycloAdd (cycloScale k a) (cycloScale k b) := by
  cases a; cases b
  simp [cycloScale, cycloAdd, Int.mul_add]

theorem cycloMul_scale_right (k : Int) (a b : Cyclo8) :
    a * cycloScale k b = cycloScale k (a * b) := by
  rw [cyclo_mul_comm a, ← cycloScale_mul_left, cyclo_mul_comm b a]

theorem dyadicMultiply_add_equiv (a b c : DyadicCyclo) :
    dyadicEquivalent (dyadicMultiply a (dyadicAdd b c))
      (dyadicAdd (dyadicMultiply a b) (dyadicMultiply a c)) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases c with | mk cn ce =>
        simp only [dyadicEquivalent, dyadicMultiply, dyadicAdd, Int.pow_add]
        change cycloScale _ (an * (cycloScale (2 ^ ce) bn + cycloScale (2 ^ be) cn)) = _
        rw [cyclo_mul_add, cycloMul_scale_right, cycloMul_scale_right]
        change cycloScale _ (cycloAdd (cycloScale (2 ^ ce) (an * bn)) (cycloScale (2 ^ be) (an * cn))) = _
        simp only [cycloScale_add, cycloScale_mul]
        congr 1 <;> congr 1 <;> simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]


theorem exactMul_add (a b c : ExactAmplitude) :
    exactMul a (exactAdd b c) = exactAdd (exactMul a b) (exactMul a c) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change exactOfDyadic (dyadicMultiply a (dyadicAdd b c)) =
          exactOfDyadic (dyadicAdd (dyadicMultiply a b) (dyadicMultiply a c))
        exact Quotient.sound (dyadicMultiply_add_equiv a b c)

theorem exactAdd_mul (a b c : ExactAmplitude) :
    exactMul (exactAdd a b) c = exactAdd (exactMul a c) (exactMul b c) := by
  rw [exactMul_comm (exactAdd a b) c, exactMul_add, exactMul_comm c a, exactMul_comm c b]

end SectorSimulation
