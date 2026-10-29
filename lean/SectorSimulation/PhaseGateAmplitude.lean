import SectorSimulation.CNOTAmplitude
namespace SectorSimulation

/-- Flip one computational-basis bit. -/
def flipWire {n : Nat} (wire : Fin n) (x : BinaryVector n) : BinaryVector n :=
  fun i => if i = wire then !(x i) else x i

/-- Standard X and Z coefficient actions over any type with negation. -/
def applyXAmplitude {n : Nat} {A : Type} (wire : Fin n)
    (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun x => state (flipWire wire x)

def applyZAmplitude {n : Nat} {A : Type} [Neg A] (wire : Fin n)
    (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun x => if x wire then -state x else state x

theorem flipWire_involutive {n : Nat} (wire : Fin n) (x : BinaryVector n) :
    flipWire wire (flipWire wire x) = x := by
  funext i
  by_cases h : i = wire <;> simp [flipWire, h]

theorem X_amplitude_involutive {n : Nat} {A : Type} (wire : Fin n)
    (state : BasisAmplitudes n A) : applyXAmplitude wire (applyXAmplitude wire state) = state := by
  funext x
  simp [applyXAmplitude, flipWire_involutive]

theorem Z_amplitude_involutive {n : Nat} {A : Type} [Neg A]
    (hneg : ∀ a : A, -(-a) = a) (wire : Fin n) (state : BasisAmplitudes n A) :
    applyZAmplitude wire (applyZAmplitude wire state) = state := by
  funext x
  cases h : x wire <;> simp [applyZAmplitude, h, hneg]

/-- In execution order X, Z, X, Z, the compiler's constant term is global minus. -/
theorem XZXZ_constant_phase {n : Nat} {A : Type} [Neg A]
    (wire : Fin n) (state : BasisAmplitudes n A) :
    applyZAmplitude wire (applyXAmplitude wire (applyZAmplitude wire (applyXAmplitude wire state))) =
      (fun x => -state x) := by
  funext x
  have hf : flipWire wire x wire = !(x wire) := by simp [flipWire]
  cases h : x wire <;> simp [applyZAmplitude, applyXAmplitude, hf, flipWire_involutive, h]

end SectorSimulation
