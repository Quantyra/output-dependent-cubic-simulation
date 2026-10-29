import SectorSimulation.HadamardBasisExpansion
namespace SectorSimulation

/-- The one-wire Walsh sign is negative only when input and output bits are both one. -/
def oneWireBasisKernel {n : Nat} (wire : Fin n) (f : BinaryVector n → ExactAmplitude)
    (basis x : BinaryVector n) : ExactAmplitude :=
  if x = basis ∨ flipWire wire x = basis then
    if x wire && basis wire then exactNeg (exactMul exactHadamardScale (f basis))
    else exactMul exactHadamardScale (f basis)
  else exactZero

theorem hadamardKernelStep_basis {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) :
    hadamardKernelStep wire (basisTerm f basis) x = oneWireBasisKernel wire f basis x := by
  have hf : flipWire wire x wire = !(x wire) := by simp [flipWire]
  by_cases h0 : x = basis
  · have h1 : flipWire wire x ≠ basis := by
      intro h
      have eq := congrFun h wire
      have eq0 := congrFun h0 wire
      rw [hf, eq0] at eq
      cases hx : basis wire <;> simp [hx] at eq
    subst basis
    cases hx : x wire <;>
      simp [hadamardKernelStep, oneWireBasisKernel, basisTerm, hx, h1,
        exactSub_eq_add_neg, exactNeg_zero, exactAdd_zero, exactZero_add, exactMul_zero, exactMul_neg]
  · by_cases h1 : flipWire wire x = basis
    · have hb : basis wire = !(x wire) := by
        have eq := congrFun h1 wire
        rw [hf] at eq
        exact eq.symm
      cases hx : x wire <;>
        simp [hadamardKernelStep, oneWireBasisKernel, basisTerm, hx, h0, h1, hb,
          exactSub_eq_add_neg, exactNeg_zero, exactAdd_zero, exactZero_add, exactMul_zero, exactMul_neg]
    · cases hx : x wire <;>
        simp [hadamardKernelStep, oneWireBasisKernel, basisTerm, hx, h0, h1,
          exactSub_eq_add_neg, exactNeg_zero, exactAdd_zero, exactZero_add, exactMul_zero, exactMul_neg]


/-- A single Hadamard on an arbitrary state is the finite sum of its one-bit Walsh kernels. -/
theorem hadamardKernel_oneWire_sum {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel [wire] f x =
      (binaryBasis n).foldr (fun basis acc => exactAdd (oneWireBasisKernel wire f basis x) acc) exactZero := by
  have h := hadamardKernel_basisExpansion [wire] f x
  simpa only [hadamardKernel, hadamardKernelStep_basis] using h

end SectorSimulation
