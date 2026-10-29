import SectorSimulation.HadamardGeneral
namespace SectorSimulation

/-- Coefficients of 1, z, z^2, z^3 with z^4 = -1. -/
structure Cyclo8 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving DecidableEq, Repr

def cycloAdd (a b : Cyclo8) : Cyclo8 :=
  ⟨a.c0+b.c0, a.c1+b.c1, a.c2+b.c2, a.c3+b.c3⟩

def cycloSub (a b : Cyclo8) : Cyclo8 :=
  ⟨a.c0-b.c0, a.c1-b.c1, a.c2-b.c2, a.c3-b.c3⟩

def cycloMul (a b : Cyclo8) : Cyclo8 :=
  ⟨a.c0*b.c0-a.c1*b.c3-a.c2*b.c2-a.c3*b.c1,
   a.c0*b.c1+a.c1*b.c0-a.c2*b.c3-a.c3*b.c2,
   a.c0*b.c2+a.c1*b.c1+a.c2*b.c0-a.c3*b.c3,
   a.c0*b.c3+a.c1*b.c2+a.c2*b.c1+a.c3*b.c0⟩

instance : Add Cyclo8 := ⟨cycloAdd⟩
instance : Sub Cyclo8 := ⟨cycloSub⟩
instance : Mul Cyclo8 := ⟨cycloMul⟩

def cycloOne : Cyclo8 := ⟨1,0,0,0⟩
def cycloMinusOne : Cyclo8 := ⟨-1,0,0,0⟩
def cycloOmega : Cyclo8 := ⟨0,1,0,0⟩
def cycloOmegaInv : Cyclo8 := ⟨0,0,0,-1⟩
/-- Twice 1/sqrt(2), expressed as z - z^3. -/
def cycloSqrtTwo : Cyclo8 := ⟨0,1,0,-1⟩

theorem cyclo_mul_add (a b c : Cyclo8) : a * (b+c) = a*b + a*c := by
  change cycloMul a (cycloAdd b c) = cycloAdd (cycloMul a b) (cycloMul a c)
  cases a; cases b; cases c
  simp only [cycloMul, cycloAdd, Cyclo8.mk.injEq, Int.mul_add]
  constructor <;> omega

theorem cyclo_mul_sub (a b c : Cyclo8) : a * (b-c) = a*b - a*c := by
  change cycloMul a (cycloSub b c) = cycloSub (cycloMul a b) (cycloMul a c)
  cases a; cases b; cases c
  simp only [cycloMul, cycloSub, Cyclo8.mk.injEq, Int.mul_sub]
  constructor <;> omega

theorem cyclo_mul_comm (a b : Cyclo8) : a*b = b*a := by
  change cycloMul a b = cycloMul b a
  cases a; cases b
  simp only [cycloMul, Cyclo8.mk.injEq]
  constructor <;> simp only [Int.mul_comm] <;> omega

theorem cyclo_omega_inverse : cycloOmega * cycloOmegaInv = cycloOne := by decide

theorem cyclo_omega_fourth : ((cycloOmega * cycloOmega) * cycloOmega) * cycloOmega = cycloMinusOne := by decide

theorem cyclo_sqrt_two_squared : cycloSqrtTwo * cycloSqrtTwo = ⟨2,0,0,0⟩ := by decide

theorem cyclo_hadamard_commutes_phase {n : Nat} (wire : Fin n)
    (factor : BinaryVector n → Cyclo8)
    (hinv : ∀ x, factor (flipWire wire x) = factor x)
    (state : BasisAmplitudes n Cyclo8) :
    hadamardGeneral wire (diagonalGeneral factor state) =
      diagonalGeneral factor (hadamardGeneral wire state) := by
  exact hadamard_commutes_invariant_diagonal cyclo_mul_add cyclo_mul_sub wire factor hinv state

end SectorSimulation
