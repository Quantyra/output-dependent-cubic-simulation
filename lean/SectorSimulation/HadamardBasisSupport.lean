import SectorSimulation.HadamardBasisKernel
namespace SectorSimulation

/-- A Hadamard step returns zero if both entries in its two-point fiber are zero. -/
theorem hadamardKernelStep_zeroFiber {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n)
    (h0 : f x = exactZero) (h1 : f (flipWire wire x) = exactZero) :
    hadamardKernelStep wire f x = exactZero := by
  cases hx : x wire <;>
    simp [hadamardKernelStep, hx, h0, h1, exactSub_eq_add_neg,
      exactNeg_zero, exactAdd_zero, exactMul_zero]

/-- Hadamards on other wires preserve a zero condition on a chosen bit. -/
theorem hadamardKernel_preserves_bitZero {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (bit : Fin n) (value : Bool)
    (hbit : bit ∉ wires) (hf : ∀ y, y bit ≠ value → f y = exactZero)
    (x : BinaryVector n) (hx : x bit ≠ value) :
    hadamardKernel wires f x = exactZero := by
  induction wires generalizing f with
  | nil => exact hf x hx
  | cons wire rest ih =>
    have hne : bit ≠ wire := by intro he; apply hbit; simp [he]
    have hrest : bit ∉ rest := by intro hm; exact hbit (by simp [hm])
    have hstep : ∀ y, y bit ≠ value → hadamardKernelStep wire f y = exactZero := by
      intro y hy
      apply hadamardKernelStep_zeroFiber wire f y (hf y hy)
      apply hf
      simpa [flipWire, hne] using hy
    exact ih (hadamardKernelStep wire f) hrest hstep

/-- A point-supported input remains zero if an untouched bit differs. -/
theorem hadamardKernel_basis_support {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n)
    (bit : Fin n) (hbit : bit ∉ wires) (hx : x bit ≠ basis bit) :
    hadamardKernel wires (basisTerm f basis) x = exactZero := by
  apply hadamardKernel_preserves_bitZero wires (basisTerm f basis) bit (basis bit) hbit
  · intro y hy
    have hn : y ≠ basis := by intro he; exact hy (congrFun he bit)
    simp [basisTerm, hn]
  · exact hx


/-- Any nonzero basis output agrees with the input on all untouched wires. -/
theorem hadamardKernel_basis_nonzero_agrees {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n)
    (h : hadamardKernel wires (basisTerm f basis) x ≠ exactZero) :
    ∀ bit, bit ∉ wires → x bit = basis bit := by
  intro bit hbit
  by_cases hx : x bit = basis bit
  · exact hx
  · exact False.elim (h (hadamardKernel_basis_support wires f basis x bit hbit hx))

end SectorSimulation
