import SectorSimulation.RecordedPairPhase
namespace SectorSimulation

theorem bilinear_equal_of_unit_pairs {n : Nat}
    (B C : BinaryVector n → BinaryVector n → Bool)
    (bl : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (br : ∀ z a b, B z (binaryShift a b) = Bool.xor (B z a) (B z b))
    (bz : ∀ z, B (fun _ => false) z = false)
    (bzr : ∀ z, B z (fun _ => false) = false)
    (cl : ∀ a b z, C (binaryShift a b) z = Bool.xor (C a z) (C b z))
    (cr : ∀ z a b, C z (binaryShift a b) = Bool.xor (C z a) (C z b))
    (cz : ∀ z, C (fun _ => false) z = false)
    (czr : ∀ z, C z (fun _ => false) = false)
    (hunit : ∀ i j, B (coordinateUnit i) (coordinateUnit j) = C (coordinateUnit i) (coordinateUnit j))
    (u v : BinaryVector n) : B u v = C u v := by
  have hrow : ∀ i, B (coordinateUnit i) v = C (coordinateUnit i) v := by
    intro i
    have hb := additive_coordinates (B (coordinateUnit i)) (br (coordinateUnit i)) (bzr (coordinateUnit i)) v
    have hc := additive_coordinates (C (coordinateUnit i)) (cr (coordinateUnit i)) (czr (coordinateUnit i)) v
    rw [hb, hc]
    congr 1
    funext j
    exact hunit i j
  have hb := additive_coordinates (fun x => B x v) (fun a b => bl a b v) (bz v) u
  have hc := additive_coordinates (fun x => C x v) (fun a b => cl a b v) (cz v) u
  rw [hb, hc]
  congr 1
  funext i
  exact hrow i
end SectorSimulation
