import SectorSimulation.CubicLayerANF
import SectorSimulation.QuadraticMasks
namespace SectorSimulation

inductive LowerPhaseTerm (n : Nat) where
  | constant (wire : Fin n)
  | linear (wire : Fin n)
  | quadratic (control target : Fin n)

def lowerPhaseMask {n : Nat} : LowerPhaseTerm n → Monomial n
  | .constant _ => fun _ => false
  | .linear wire => singletonMask wire
  | .quadratic a b => pairMask a b

def lowerPhaseRecords {n : Nat} : LowerPhaseTerm n → List NativeGate
  | .constant wire => [⟨"X", [wire.val]⟩, ⟨"Z", [wire.val]⟩, ⟨"X", [wire.val]⟩, ⟨"Z", [wire.val]⟩]
  | .linear wire => [⟨"Z", [wire.val]⟩]
  | .quadratic a b => [⟨"H", [b.val]⟩, ⟨"CX", [a.val, b.val]⟩, ⟨"H", [b.val]⟩]

def LowerPhaseTerm.valid {n : Nat} : LowerPhaseTerm n → Prop
  | .quadratic a b => a ≠ b
  | _ => True

def sharedMonomialSign {n : Nat} (m : Monomial n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if evalMonomial m x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩

theorem nativeConstantSign {n : Nat} (wire : Fin n) (state : SharedDyadicState n) :
    replayExactNative n (lowerPhaseRecords (.constant wire)) state = some (sharedNeg state) := by
  have hf : ∀ x, flipWire wire (flipWire wire x) = x := flipWire_involutive wire
  simp [lowerPhaseRecords, replayExactNative, applyExactNative, wire.isLt, sharedX, sharedZ, sharedNeg,
    flipWire, cycloNeg, hf]
  funext x
  cases hx : x wire <;> simp [hx, cycloNeg]

theorem nativeLowerPhaseTerm_correct {n : Nat} (term : LowerPhaseTerm n) (valid : term.valid)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (lowerPhaseRecords term) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (sharedMonomialSign (lowerPhaseMask term) state) x := by
  cases term with
  | constant wire =>
    refine ⟨sharedNeg state, nativeConstantSign wire state, ?_⟩
    intro x
    simp [sharedAmplitude, sharedNeg, sharedMonomialSign, lowerPhaseMask, evalMonomial_emptyMask]
  | linear wire =>
    refine ⟨sharedZ wire state, ?_, ?_⟩
    · simp [lowerPhaseRecords, replayExactNative, applyExactNative, wire.isLt]
    · intro x; simp [sharedAmplitude, sharedZ, sharedMonomialSign, lowerPhaseMask, evalMonomial_singletonMask]
  | quadratic a b =>
    have h : a ≠ b := valid
    refine ⟨sharedHadamard b (sharedCNOT a b (sharedHadamard b state)), ?_, ?_⟩
    · exact exactNative_HCXH a b h state
    · intro x
      simpa [sharedAmplitude, sharedControlledSign, sharedMonomialSign, lowerPhaseMask, evalMonomial_pairMask] using
        sharedHCXH_controlled_sign a b h state x

theorem sharedMonomialSign_congr {n : Nat} (m : Monomial n) (u v : SharedDyadicState n)
    (h : ∀ x, sharedAmplitude u x = sharedAmplitude v x) (x : BinaryVector n) :
    sharedAmplitude (sharedMonomialSign m u) x = sharedAmplitude (sharedMonomialSign m v) x := by
  cases hm : evalMonomial m x <;> simp [sharedMonomialSign, sharedAmplitude, hm] <;> try exact h x
  change exactNeg (sharedAmplitude u x) = exactNeg (sharedAmplitude v x)
  rw [h x]

def nativeLowerPhaseLayer {n : Nat} (terms : List (LowerPhaseTerm n)) : List NativeGate :=
  terms.flatMap lowerPhaseRecords

def idealLowerPhaseLayer {n : Nat} : List (LowerPhaseTerm n) → SharedDyadicState n → SharedDyadicState n
  | [], state => state
  | term :: rest, state => idealLowerPhaseLayer rest (sharedMonomialSign (lowerPhaseMask term) state)

theorem nativeLowerPhaseLayer_correct_from_equivalent {n : Nat} (terms : List (LowerPhaseTerm n))
    (valid : ∀ term ∈ terms, term.valid) (u v : SharedDyadicState n)
    (equiv : ∀ x, sharedAmplitude u x = sharedAmplitude v x) :
    ∃ result, replayExactNative n (nativeLowerPhaseLayer terms) u = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (idealLowerPhaseLayer terms v) x := by
  induction terms generalizing u v with
  | nil => exact ⟨u, rfl, equiv⟩
  | cons term rest ih =>
    have ht : term.valid := valid term (by simp)
    have hr : ∀ z ∈ rest, z.valid := by intro z hz; exact valid z (by simp [hz])
    obtain ⟨mid, hm, ha⟩ := nativeLowerPhaseTerm_correct term ht u
    have he : ∀ x, sharedAmplitude mid x = sharedAmplitude (sharedMonomialSign (lowerPhaseMask term) v) x := by
      intro x
      exact (ha x).trans (sharedMonomialSign_congr (lowerPhaseMask term) u v equiv x)
    obtain ⟨result, hresult, heq⟩ := ih hr mid (sharedMonomialSign (lowerPhaseMask term) v) he
    refine ⟨result, ?_, heq⟩
    simp only [nativeLowerPhaseLayer, List.flatMap_cons, replayExactNative_append, hm]
    exact hresult

theorem nativeLowerPhaseLayer_correct {n : Nat} (terms : List (LowerPhaseTerm n))
    (valid : ∀ term ∈ terms, term.valid) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (nativeLowerPhaseLayer terms) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (idealLowerPhaseLayer terms state) x := by
  exact nativeLowerPhaseLayer_correct_from_equivalent terms valid state state (fun _ => rfl)

end SectorSimulation
