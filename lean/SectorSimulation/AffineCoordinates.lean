import SectorSimulation.SamePolarAffine
namespace SectorSimulation

def coordinateUnit {n : Nat} (i : Fin n) : BinaryVector n := fun j => decide (j = i)
def maskedCoordinates {n : Nat} (xs : List (Fin n)) (x : BinaryVector n) : BinaryVector n :=
  fun i => x i && decide (i ∈ xs)

theorem additive_coordinates_list {n : Nat} (f : BinaryVector n → Bool)
    (hadd : ∀ u v, f (binaryShift u v) = Bool.xor (f u) (f v))
    (hzero : f (fun _ => false) = false)
    (xs : List (Fin n)) (hn : xs.Nodup) (x : BinaryVector n) :
    f (maskedCoordinates xs x) = walshWireParity xs (fun i => f (coordinateUnit i)) x := by
  induction xs with
  | nil =>
    have hm : maskedCoordinates [] x = (fun _ => false) := by
      funext i; simp [maskedCoordinates]
    simpa [hm, walshWireParity] using hzero
  | cons i rest ih =>
    have hr := List.nodup_cons.mp hn
    have he : maskedCoordinates (i :: rest) x =
        binaryShift (if x i then coordinateUnit i else (fun _ => false)) (maskedCoordinates rest x) := by
      funext j
      by_cases hji : j = i
      · subst j
        cases hx : x i <;> simp [maskedCoordinates, coordinateUnit, binaryShift, hr.1, hx]
      · cases hx : x i <;> simp [maskedCoordinates, coordinateUnit, binaryShift, hji, hx]
    rw [he, hadd, ih hr.2]
    cases hx : x i <;> simp [hx, hzero, walshWireParity]

theorem additive_coordinates {n : Nat} (f : BinaryVector n → Bool)
    (hadd : ∀ u v, f (binaryShift u v) = Bool.xor (f u) (f v))
    (hzero : f (fun _ => false) = false) (x : BinaryVector n) :
    f x = walshWireParity (List.finRange n) (fun i => f (coordinateUnit i)) x := by
  have h := additive_coordinates_list f hadd hzero (List.finRange n) (List.nodup_finRange n) x
  have hm : maskedCoordinates (List.finRange n) x = x := by
    funext i; simp [maskedCoordinates]
  simpa [hm] using h

theorem samePolar_affine_coordinates {n : Nat} (q r : BinaryVector n → Bool)
    (hpolar : ∀ u v, phasePolarFunction q u v = phasePolarFunction r u v)
    (x : BinaryVector n) :
    Bool.xor (q x) (r x) = Bool.xor (Bool.xor (q (fun _ => false)) (r (fun _ => false)))
      (walshWireParity (List.finRange n) (fun i => normalizedDifference q r (coordinateUnit i)) x) := by
  have hz : normalizedDifference q r (fun _ => false) = false := by
    simp [normalizedDifference]
  have h := additive_coordinates (normalizedDifference q r)
    (samePolar_normalizedDifference_add q r hpolar) hz x
  unfold normalizedDifference at h ⊢
  cases hq : q x <;> cases hr : r x <;> cases hq0 : q (fun _ => false) <;>
    cases hr0 : r (fun _ => false) <;> simp_all
end SectorSimulation
