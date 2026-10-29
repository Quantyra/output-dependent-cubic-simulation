import SectorSimulation.CyclotomicEight
namespace SectorSimulation

/-- Exact T/TDG multipliers in the eighth-root coefficient model. -/
def cycloTPhase {n : Nat} (phaseWire : Fin n) (inverse : Bool) (x : BinaryVector n) : Cyclo8 :=
  if x phaseWire then (if inverse then cycloOmegaInv else cycloOmega) else cycloOne

theorem cycloTPhase_flip_invariant {n : Nat} (hwire phaseWire : Fin n)
    (h : phaseWire ≠ hwire) (inverse : Bool) (x : BinaryVector n) :
    cycloTPhase phaseWire inverse (flipWire hwire x) = cycloTPhase phaseWire inverse x := by
  simp [cycloTPhase, flipWire, h]

theorem cycloT_commutes_hadamard {n : Nat} (hwire phaseWire : Fin n)
    (h : phaseWire ≠ hwire) (inverse : Bool) (state : BasisAmplitudes n Cyclo8) :
    hadamardGeneral hwire (diagonalGeneral (cycloTPhase phaseWire inverse) state) =
      diagonalGeneral (cycloTPhase phaseWire inverse) (hadamardGeneral hwire state) := by
  apply cyclo_hadamard_commutes_phase
  exact cycloTPhase_flip_invariant hwire phaseWire h inverse

/-- The exact numerator z-z^3 commutes across any two coefficient multiplications. -/
theorem cyclo_sqrt_two_central (a b : Cyclo8) :
    cycloSqrtTwo * (a*b) = a*(cycloSqrtTwo*b) := by
  change cycloMul cycloSqrtTwo (cycloMul a b) = cycloMul a (cycloMul cycloSqrtTwo b)
  cases a; cases b
  simp only [cycloSqrtTwo, cycloMul, Cyclo8.mk.injEq, Int.mul_add, Int.mul_sub, Int.one_mul, Int.zero_mul, Int.mul_zero, Int.neg_mul, Int.mul_neg]
  constructor <;> (try simp only [Int.mul_comm]) <;> omega

theorem cycloT_commutes_scaled_hadamard {n : Nat} (hwire phaseWire : Fin n)
    (h : phaseWire ≠ hwire) (inverse : Bool) (state : BasisAmplitudes n Cyclo8) :
    scaledHadamard cycloSqrtTwo hwire (diagonalGeneral (cycloTPhase phaseWire inverse) state) =
      diagonalGeneral (cycloTPhase phaseWire inverse) (scaledHadamard cycloSqrtTwo hwire state) := by
  exact scaledHadamard_commutes_invariant_diagonal cyclo_mul_add cyclo_mul_sub cycloSqrtTwo
    cyclo_sqrt_two_central hwire (cycloTPhase phaseWire inverse)
    (cycloTPhase_flip_invariant hwire phaseWire h inverse) state

end SectorSimulation
