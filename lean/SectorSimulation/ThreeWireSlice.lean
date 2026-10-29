import SectorSimulation.ToffoliAllVectors
namespace SectorSimulation

/-- Embed a three-bit bits vector while preserving all other wires of the base vector. -/
def embedThree {n : Nat} (w : Fin 3 → Fin n) (base : BinaryVector n) (bits : BinaryVector 3) : BinaryVector n :=
  fun j => if j = w 0 then bits 0 else if j = w 1 then bits 1 else if j = w 2 then bits 2 else base j

def sliceThree {n : Nat} (w : Fin 3 → Fin n) (base : BinaryVector n)
    (state : SharedDyadicState n) : SharedDyadicState 3 :=
  ⟨fun bits => state.numerator (embedThree w base bits), state.exponent⟩

theorem embedThree_at {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (bits : BinaryVector 3) (i : Fin 3) :
    embedThree w base bits (w i) = bits i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    have bound := i.isLt
    omega
  have h01 : w 0 ≠ w 1 := by intro h; have hh := hw h; exact (by decide : (0 : Fin 3) ≠ 1) hh
  have h02 : w 0 ≠ w 2 := by intro h; have hh := hw h; exact (by decide : (0 : Fin 3) ≠ 2) hh
  have h12 : w 1 ≠ w 2 := by intro h; have hh := hw h; exact (by decide : (1 : Fin 3) ≠ 2) hh
  rcases hi with hi | hi | hi <;> subst i <;> simp [embedThree, h01, h02, h12, Ne.symm]

theorem embedThree_flip {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (bits : BinaryVector 3) (i : Fin 3) :
    embedThree w base (flipWire i bits) = flipWire (w i) (embedThree w base bits) := by
  funext j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    have bound := i.isLt
    omega
  have h01 : w 0 ≠ w 1 := by intro h; have hh := hw h; exact (by decide : (0 : Fin 3) ≠ 1) hh
  have h02 : w 0 ≠ w 2 := by intro h; have hh := hw h; exact (by decide : (0 : Fin 3) ≠ 2) hh
  have h12 : w 1 ≠ w 2 := by intro h; have hh := hw h; exact (by decide : (1 : Fin 3) ≠ 2) hh
  rcases hi with hi | hi | hi <;> subst i <;> simp [embedThree, flipWire, h01, h02, h12, Ne.symm]
  all_goals by_cases hj1 : j = w 1 <;> by_cases hj2 : j = w 2 <;> simp_all [h01, h02, h12, Ne.symm]

theorem sliceThree_hadamard {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) (i : Fin 3) :
    sliceThree w base (sharedHadamard (w i) state) = sharedHadamard i (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedHadamard, cycloHadamardNumerator, embedThree_at w hw, embedThree_flip w hw]

theorem sliceThree_x {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) (i : Fin 3) :
    sliceThree w base (sharedX (w i) state) = sharedX i (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedX, embedThree_flip w hw]

theorem sliceThree_z {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) (i : Fin 3) :
    sliceThree w base (sharedZ (w i) state) = sharedZ i (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedZ, embedThree_at w hw]

theorem sliceThree_t {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) (i : Fin 3) (inverse : Bool) :
    sliceThree w base (sharedT (w i) inverse state) = sharedT i inverse (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedT, embedThree_at w hw]

theorem applyCNOT_as_flip {n : Nat} (control target : Fin n) (x : BinaryVector n) :
    applyCNOT control target x = if x control then flipWire target x else x := by
  funext j
  simp only [applyCNOT, vectorAddRow, flipWire]
  cases hc : x control <;> simp [hc]
  all_goals (try simp [flipWire])
  all_goals grind

theorem embedThree_cnot {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (bits : BinaryVector 3) (control target : Fin 3) :
    embedThree w base (applyCNOT control target bits) =
      applyCNOT (w control) (w target) (embedThree w base bits) := by
  cases h : bits control <;> simp [applyCNOT_as_flip, embedThree_at w hw, embedThree_flip w hw, h]

theorem sliceThree_cnot {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) (control target : Fin 3) :
    sliceThree w base (sharedCNOT (w control) (w target) state) =
      sharedCNOT control target (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedCNOT, embedThree_cnot w hw]

end SectorSimulation
