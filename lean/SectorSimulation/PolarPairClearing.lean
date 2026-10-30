import SectorSimulation.BooleanSource
namespace SectorSimulation

def selectedBinaryVector {n : Nat} (b : Bool) (x : BinaryVector n) : BinaryVector n :=
  if b then x else fun _ => false

def clearPolarPair {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x : BinaryVector n) : BinaryVector n :=
  binaryShift x (binaryShift (selectedBinaryVector (B x v) u) (selectedBinaryVector (B x u) v))

theorem clearPolarPair_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x : BinaryVector n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (huu : B u u = false) (hvv : B v v = false)
    (huv : B u v = true) (hvu : B v u = true) :
    B (clearPolarPair B u v x) u = false ∧ B (clearPolarPair B u v x) v = false := by
  cases hxu : B x u <;> cases hxv : B x v <;>
    simp [clearPolarPair, selectedBinaryVector, hadd, hzero, huu, hvv, huv, hvu, hxu, hxv]

theorem clearPolarPair_preserves {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x z : BinaryVector n)
    (hadd : ∀ a b w, B (binaryShift a b) w = Bool.xor (B a w) (B b w))
    (hzero : ∀ w, B (fun _ => false) w = false)
    (huz : B u z = false) (hvz : B v z = false) :
    B (clearPolarPair B u v x) z = B x z := by
  cases hxu : B x u <;> cases hxv : B x v <;>
    simp [clearPolarPair, selectedBinaryVector, hadd, hzero, huz, hvz, hxu, hxv]


theorem clearPolarPair_reconstruct {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x : BinaryVector n) :
    binaryShift (clearPolarPair B u v x)
      (binaryShift (selectedBinaryVector (B x v) u) (selectedBinaryVector (B x u) v)) = x := by
  funext i
  simp only [clearPolarPair, binaryShift]
  cases x i <;> cases selectedBinaryVector (B x v) u i <;>
    cases selectedBinaryVector (B x u) v i <;> rfl

theorem clearPolarPair_fixed {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x : BinaryVector n) (hu : B x u = false) (hv : B x v = false) :
    clearPolarPair B u v x = x := by
  funext i
  simp [clearPolarPair, selectedBinaryVector, binaryShift, hu, hv]

theorem clearPolarPair_idempotent {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v x : BinaryVector n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (huu : B u u = false) (hvv : B v v = false)
    (huv : B u v = true) (hvu : B v u = true) :
    clearPolarPair B u v (clearPolarPair B u v x) = clearPolarPair B u v x := by
  obtain ⟨hu,hv⟩ := clearPolarPair_orthogonal B u v x hadd hzero huu hvv huv hvu
  exact clearPolarPair_fixed B u v (clearPolarPair B u v x) hu hv

end SectorSimulation
