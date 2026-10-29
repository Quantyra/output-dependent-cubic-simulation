import SectorSimulation.HadamardBasisSupport
namespace SectorSimulation

def basisSameCoefficient {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (basis : BinaryVector n) : ExactAmplitude :=
  if basis wire then exactNeg (exactMul exactHadamardScale (f basis))
  else exactMul exactHadamardScale (f basis)

def basisFlipCoefficient {n : Nat} (f : BinaryVector n → ExactAmplitude)
    (basis : BinaryVector n) : ExactAmplitude := exactMul exactHadamardScale (f basis)

theorem hadamardKernelStep_basis_split {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) :
    hadamardKernelStep wire (basisTerm f basis) x =
      exactAdd (basisTerm (fun _ => basisSameCoefficient wire f basis) basis x)
        (basisTerm (fun _ => basisFlipCoefficient f basis) (flipWire wire basis) x) := by
  rw [hadamardKernelStep_basis]
  have hne : flipWire wire basis ≠ basis := by
    intro he
    have hbit := congrFun he wire
    simp [flipWire] at hbit
  by_cases h0 : x = basis
  · subst x
    cases hb : basis wire <;>
      simp [oneWireBasisKernel, basisTerm, basisSameCoefficient, basisFlipCoefficient,
        hb, hne, Ne.symm hne, exactAdd_zero, exactZero_add]
  · by_cases h1 : x = flipWire wire basis
    · subst x
      have hflip : flipWire wire (flipWire wire basis) = basis := flipWire_involutive wire basis
      have hw : flipWire wire basis wire = !(basis wire) := by simp [flipWire]
      cases hb : basis wire <;>
        simp [oneWireBasisKernel, basisTerm, basisSameCoefficient, basisFlipCoefficient,
          hb, hne, hflip, hw, exactAdd_zero, exactZero_add]
    · have h2 : flipWire wire x ≠ basis := by
        intro he
        have hh := congrArg (flipWire wire) he
        simp only [flipWire_involutive] at hh
        exact h1 hh
      simp [oneWireBasisKernel, basisTerm, basisSameCoefficient, basisFlipCoefficient,
        h0, h1, h2, exactAdd_zero]

theorem hadamardKernel_basis_split {n : Nat} (wire : Fin n) (rest : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) :
    hadamardKernel (wire :: rest) (basisTerm f basis) x =
      exactAdd
        (hadamardKernel rest (basisTerm (fun _ => basisSameCoefficient wire f basis) basis) x)
        (hadamardKernel rest (basisTerm (fun _ => basisFlipCoefficient f basis) (flipWire wire basis)) x) := by
  simp only [hadamardKernel]
  have h : hadamardKernelStep wire (basisTerm f basis) =
      (fun y => exactAdd (basisTerm (fun _ => basisSameCoefficient wire f basis) basis y)
        (basisTerm (fun _ => basisFlipCoefficient f basis) (flipWire wire basis) y)) := by
    funext y; exact hadamardKernelStep_basis_split wire f basis y
  rw [h, hadamardKernel_add]


/-- Exact binary branching expansion of a point-supported input. -/
def basisBranchExpansion {n : Nat} : List (Fin n) → ExactAmplitude → BinaryVector n →
    BinaryVector n → ExactAmplitude
  | [], c, basis, x => if x = basis then c else exactZero
  | wire :: rest, c, basis, x =>
    exactAdd
      (basisBranchExpansion rest (if basis wire then exactNeg (exactMul exactHadamardScale c)
        else exactMul exactHadamardScale c) basis x)
      (basisBranchExpansion rest (exactMul exactHadamardScale c) (flipWire wire basis) x)

theorem hadamardKernel_basis_branchExpansion {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) :
    hadamardKernel wires (basisTerm f basis) x = basisBranchExpansion wires (f basis) basis x := by
  induction wires generalizing f basis with
  | nil => rfl
  | cons wire rest ih =>
    rw [hadamardKernel_basis_split]
    simp only [basisBranchExpansion]
    rw [ih, ih]
    rfl


/-- Every input amplitude is summed over all basis states and their exact branches. -/
theorem hadamardKernel_branchExpansion {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel wires f x =
      (binaryBasis n).foldr
        (fun basis acc => exactAdd (basisBranchExpansion wires (f basis) basis x) acc) exactZero := by
  have h := hadamardKernel_basisExpansion wires f x
  simpa only [hadamardKernel_basis_branchExpansion] using h

end SectorSimulation
