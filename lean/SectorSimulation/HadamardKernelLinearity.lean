import SectorSimulation.ExactDistributivity
namespace SectorSimulation

theorem exactAdd_left_comm (a b c : ExactAmplitude) :
    exactAdd a (exactAdd b c) = exactAdd b (exactAdd a c) := by
  rw [← exactAdd_assoc, exactAdd_comm a b, exactAdd_assoc]

theorem exactNeg_add (a b : ExactAmplitude) :
    exactNeg (exactAdd a b) = exactAdd (exactNeg a) (exactNeg b) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change exactOfDyadic (dyadicNeg (dyadicAdd a b)) =
        exactOfDyadic (dyadicAdd (dyadicNeg a) (dyadicNeg b))
      congr 1
      cases a with | mk an ae =>
        cases b with | mk bn be =>
          cases an; cases bn
          simp [dyadicNeg, dyadicAdd, cycloNeg, cycloAdd, cycloScale, Int.mul_neg, Int.neg_add]

theorem exactMul_neg (a b : ExactAmplitude) :
    exactMul a (exactNeg b) = exactNeg (exactMul a b) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change exactOfDyadic (dyadicMultiply a (dyadicNeg b)) =
        exactOfDyadic (dyadicNeg (dyadicMultiply a b))
      congr 1
      cases a with | mk an ae =>
        cases b with | mk bn be =>
          change DyadicCyclo.mk (cycloMul an (cycloNeg bn)) (ae + be) =
            DyadicCyclo.mk (cycloNeg (cycloMul an bn)) (ae + be)
          rw [cyclo_mul_neg_right]

theorem hadamardKernelStep_add {n : Nat} (wire : Fin n)
    (f g : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernelStep wire (fun y => exactAdd (f y) (g y)) x =
      exactAdd (hadamardKernelStep wire f x) (hadamardKernelStep wire g x) := by
  cases hx : x wire <;>
    simp [hadamardKernelStep, hx, exactSub_eq_add_neg, exactNeg_add, exactMul_add,
      exactAdd_assoc, exactAdd_comm, exactAdd_left_comm]

theorem hadamardKernel_add {n : Nat} (wires : List (Fin n))
    (f g : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel wires (fun y => exactAdd (f y) (g y)) x =
      exactAdd (hadamardKernel wires f x) (hadamardKernel wires g x) := by
  induction wires generalizing f g with
  | nil => rfl
  | cons wire rest ih =>
    simp only [hadamardKernel]
    have h : hadamardKernelStep wire (fun y => exactAdd (f y) (g y)) =
        (fun y => exactAdd (hadamardKernelStep wire f y) (hadamardKernelStep wire g y)) := by
      funext y; exact hadamardKernelStep_add wire f g y
    rw [h]
    exact ih _ _


theorem exactMul_left_comm (a b c : ExactAmplitude) :
    exactMul a (exactMul b c) = exactMul b (exactMul a c) := by
  rw [← exactMul_assoc, exactMul_comm a b, exactMul_assoc]

theorem hadamardKernelStep_scale {n : Nat} (wire : Fin n) (c : ExactAmplitude)
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernelStep wire (fun y => exactMul c (f y)) x =
      exactMul c (hadamardKernelStep wire f x) := by
  cases hx : x wire <;>
    simp [hadamardKernelStep, hx, exactSub_eq_add_neg, exactMul_add, exactMul_neg,
      exactMul_assoc, exactMul_left_comm]

theorem hadamardKernel_scale {n : Nat} (wires : List (Fin n)) (c : ExactAmplitude)
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel wires (fun y => exactMul c (f y)) x =
      exactMul c (hadamardKernel wires f x) := by
  induction wires generalizing f with
  | nil => rfl
  | cons wire rest ih =>
    simp only [hadamardKernel]
    have h : hadamardKernelStep wire (fun y => exactMul c (f y)) =
        (fun y => exactMul c (hadamardKernelStep wire f y)) := by
      funext y; exact hadamardKernelStep_scale wire c f y
    rw [h]
    exact ih _

end SectorSimulation
