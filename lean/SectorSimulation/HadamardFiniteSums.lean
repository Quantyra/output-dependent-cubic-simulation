import SectorSimulation.HadamardKernelLinearity
namespace SectorSimulation

def exactZero : ExactAmplitude := exactOfDyadic ⟨⟨0, 0, 0, 0⟩, 0⟩

theorem exactAdd_zero (a : ExactAmplitude) : exactAdd a exactZero = a := by
  induction a using Quotient.ind with
  | _ a =>
    change exactOfDyadic (dyadicAdd a ⟨⟨0,0,0,0⟩,0⟩) = exactOfDyadic a
    congr 1
    cases a with | mk an ae =>
      cases an
      simp [dyadicAdd, cycloAdd, cycloScale]

theorem exactNeg_zero : exactNeg exactZero = exactZero := by
  rfl

theorem exactMul_zero (a : ExactAmplitude) : exactMul a exactZero = exactZero := by
  induction a using Quotient.ind with
  | _ a =>
    change exactOfDyadic (dyadicMultiply a ⟨⟨0,0,0,0⟩,0⟩) = exactOfDyadic ⟨⟨0,0,0,0⟩,0⟩
    apply Quotient.sound
    change dyadicEquivalent (dyadicMultiply a ⟨⟨0,0,0,0⟩,0⟩) ⟨⟨0,0,0,0⟩,0⟩
    have hz : ∀ a : Cyclo8, a * ⟨0,0,0,0⟩ = ⟨0,0,0,0⟩ := by
      intro a
      cases a
      change cycloMul _ _ = _
      simp [cycloMul]
    cases a with | mk an ae =>
      simp only [dyadicEquivalent, dyadicMultiply]
      rw [hz]
      simp [cycloScale]

theorem hadamardKernel_zero {n : Nat} (wires : List (Fin n)) (x : BinaryVector n) :
    hadamardKernel wires (fun _ => exactZero) x = exactZero := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    simp only [hadamardKernel]
    have h : hadamardKernelStep wire (fun _ => exactZero) = (fun _ => exactZero) := by
      funext y
      cases hy : y wire <;>
        simp [hadamardKernelStep, hy, exactSub_eq_add_neg, exactNeg_zero, exactAdd_zero, exactMul_zero]
    rw [h]
    exact ih

def exactFunctionSum {n : Nat} {α : Type} (items : List α)
    (f : α → BinaryVector n → ExactAmplitude) : BinaryVector n → ExactAmplitude :=
  fun x => items.foldr (fun a acc => exactAdd (f a x) acc) exactZero

theorem hadamardKernel_sum {n : Nat} {α : Type} (wires : List (Fin n))
    (items : List α) (f : α → BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel wires (exactFunctionSum items f) x =
      items.foldr (fun a acc => exactAdd (hadamardKernel wires (f a) x) acc) exactZero := by
  induction items with
  | nil => exact hadamardKernel_zero wires x
  | cons a rest ih =>
    change hadamardKernel wires (fun y => exactAdd (f a y) (exactFunctionSum rest f y)) x = _
    rw [hadamardKernel_add, ih]
    rfl

end SectorSimulation
