import SectorSimulation.HadamardCommutation
namespace SectorSimulation

/-- Hadamard numerator over an arbitrary additive coefficient type. -/
def hadamardGeneral {n : Nat} {A : Type} [Add A] [Sub A]
    (wire : Fin n) (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun x => if x wire then state (flipWire wire x) - state x else state x + state (flipWire wire x)

/-- A diagonal multiplier, including control-only T and TDG phases. -/
def diagonalGeneral {n : Nat} {A : Type} [Mul A]
    (factor : BinaryVector n → A) (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun x => factor x * state x

theorem hadamard_commutes_invariant_diagonal {n : Nat} {A : Type}
    [Add A] [Sub A] [Mul A]
    (mul_add : ∀ a b c : A, a * (b + c) = a*b + a*c)
    (mul_sub : ∀ a b c : A, a * (b - c) = a*b - a*c)
    (wire : Fin n) (factor : BinaryVector n → A)
    (hinv : ∀ x, factor (flipWire wire x) = factor x)
    (state : BasisAmplitudes n A) :
    hadamardGeneral wire (diagonalGeneral factor state) =
      diagonalGeneral factor (hadamardGeneral wire state) := by
  funext x
  simp only [hadamardGeneral, diagonalGeneral]
  rw [hinv x]
  cases hw : x wire <;> simp [mul_add, mul_sub]

theorem hadamard_general_commutes_disjoint_CNOT {n : Nat} {A : Type}
    [Add A] [Sub A] (wire control target : Fin n)
    (hwc : wire ≠ control) (hwt : wire ≠ target)
    (state : BasisAmplitudes n A) :
    hadamardGeneral wire (applyCNOTAmplitude (control,target) state) =
      applyCNOTAmplitude (control,target) (hadamardGeneral wire state) := by
  funext x
  have hw : applyCNOT control target x wire = x wire := by
    simp [applyCNOT, vectorAddRow, hwt]
  simp only [hadamardGeneral, applyCNOTAmplitude]
  rw [hw, cnot_flip_commute wire control target hwc hwt x]

/-- The same commutation holds after multiplying by any fixed normalization factor. -/
def scaledHadamard {n : Nat} {A : Type} [Add A] [Sub A] [Mul A]
    (scale : A) (wire : Fin n) (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun x => scale * hadamardGeneral wire state x

theorem scaledHadamard_commutes_disjoint_CNOT {n : Nat} {A : Type}
    [Add A] [Sub A] [Mul A] (scale : A) (wire control target : Fin n)
    (hwc : wire ≠ control) (hwt : wire ≠ target)
    (state : BasisAmplitudes n A) :
    scaledHadamard scale wire (applyCNOTAmplitude (control,target) state) =
      applyCNOTAmplitude (control,target) (scaledHadamard scale wire state) := by
  funext x
  have h := congrFun (hadamard_general_commutes_disjoint_CNOT wire control target hwc hwt state) x
  exact congrArg (fun a => scale * a) h

theorem scaledHadamard_commutes_invariant_diagonal {n : Nat} {A : Type}
    [Add A] [Sub A] [Mul A]
    (mul_add : ∀ a b c : A, a * (b + c) = a*b + a*c)
    (mul_sub : ∀ a b c : A, a * (b - c) = a*b - a*c)
    (scale : A) (scale_commutes : ∀ a b : A, scale * (a*b) = a*(scale*b))
    (wire : Fin n) (factor : BinaryVector n → A)
    (hinv : ∀ x, factor (flipWire wire x) = factor x)
    (state : BasisAmplitudes n A) :
    scaledHadamard scale wire (diagonalGeneral factor state) =
      diagonalGeneral factor (scaledHadamard scale wire state) := by
  funext x
  have h := congrFun (hadamard_commutes_invariant_diagonal mul_add mul_sub wire factor hinv state) x
  change scale * hadamardGeneral wire (diagonalGeneral factor state) x =
    factor x * (scale * hadamardGeneral wire state x)
  rw [h]
  exact scale_commutes (factor x) (hadamardGeneral wire state x)

end SectorSimulation
