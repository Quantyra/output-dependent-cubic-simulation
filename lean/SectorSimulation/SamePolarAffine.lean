import SectorSimulation.WalshPolarSquare
namespace SectorSimulation

def normalizedDifference {n : Nat} (q r : BinaryVector n → Bool) (x : BinaryVector n) : Bool :=
  Bool.xor (Bool.xor (q x) (r x)) (Bool.xor (q (fun _ => false)) (r (fun _ => false)))

theorem samePolar_normalizedDifference_add {n : Nat} (q r : BinaryVector n → Bool)
    (hpolar : ∀ u v, phasePolarFunction q u v = phasePolarFunction r u v)
    (u v : BinaryVector n) :
    normalizedDifference q r (binaryShift u v) =
      Bool.xor (normalizedDifference q r u) (normalizedDifference q r v) := by
  have h := hpolar u v
  simp only [phasePolarFunction] at h
  simp only [normalizedDifference]
  cases h0 : q (binaryShift u v) <;> cases h1 : r (binaryShift u v) <;>
    cases h2 : q u <;> cases h3 : r u <;> cases h4 : q v <;> cases h5 : r v <;>
    cases h6 : q (fun _ => false) <;> cases h7 : r (fun _ => false) <;> simp_all
end SectorSimulation
