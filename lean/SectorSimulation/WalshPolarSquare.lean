import SectorSimulation.CanonicalVectorWalsh
import SectorSimulation.BinaryShift
namespace SectorSimulation

theorem binaryShift_basis_perm {n : Nat} (j : BinaryVector n) :
    ((binaryBasis n).map (binaryShift j)).Perm (binaryBasis n) := by
  have hinj : Function.Injective (binaryShift j) := by
    intro a b h
    have h' := congrArg (binaryShift j) h
    simpa only [binaryShift_involutive] using h'
  have hn : ((binaryBasis n).map (binaryShift j)).Nodup := by
    exact List.Pairwise.map _ (fun _ _ h h' => h (hinj h')) (binaryBasis_nodup n)
  apply List.perm_iff_count.mpr
  intro x
  rw [hn.count, (binaryBasis_nodup n).count]
  have hm : x ∈ (binaryBasis n).map (binaryShift j) :=
    List.mem_map.mpr ⟨binaryShift j x, binaryBasis_complete _, binaryShift_involutive j x⟩
  simp [hm, binaryBasis_complete]

theorem integerWalshSign_xor (a b : Bool) :
    integerWalshSign (Bool.xor a b) = integerWalshSign a * integerWalshSign b := by
  cases a <;> cases b <;> rfl

theorem integerWalshSign_not (a : Bool) : integerWalshSign (!a) = -integerWalshSign a := by
  cases a <;> rfl

theorem integerSum_map_neg {α : Type} (xs : List α) (f : α → Int) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [ih, Int.neg_add]

theorem shiftedSignSum_cancel {n : Nat} (f : BinaryVector n → Bool) (j : BinaryVector n)
    (hflip : ∀ x, f (binaryShift j x) = !f x) :
    ((binaryBasis n).map (fun x => integerWalshSign (f x))).sum = 0 := by
  let g := fun x : BinaryVector n => integerWalshSign (f x)
  have hp := integerSum_perm _ _ (binaryShift_basis_perm j).symm g
  have he : ((binaryBasis n).map g).sum = -((binaryBasis n).map g).sum := by
    simpa [g, List.map_map, Function.comp_def, hflip, integerWalshSign_not, integerSum_map_neg] using hp
  dsimp [g] at he
  omega


theorem integerSum_mul_right {α : Type} (xs : List α) (f : α → Int) (v : Int) :
    (xs.map f).sum * v = (xs.map (fun x => f x * v)).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [Int.add_mul, ih]

theorem integerMul_sum_left {α : Type} (v : Int) (xs : List α) (f : α → Int) :
    v * (xs.map f).sum = (xs.map (fun x => v * f x)).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [Int.mul_add, ih]

theorem integerSquare_doubleSum {α : Type} (xs : List α) (f : α → Int) :
    (xs.map f).sum * (xs.map f).sum =
      (xs.map (fun x => (xs.map (fun y => f x * f y)).sum)).sum := by
  rw [integerSum_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  exact integerMul_sum_left (f x) xs f

theorem binaryShift_doubleSum {n : Nat} (f : BinaryVector n → BinaryVector n → Int) :
    ((binaryBasis n).map (fun x => ((binaryBasis n).map (f x)).sum)).sum =
      ((binaryBasis n).map (fun x => ((binaryBasis n).map (fun u => f x (binaryShift x u))).sum)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  have h := integerSum_perm _ _ (binaryShift_basis_perm x).symm (f x)
  simpa [List.map_map, Function.comp_def] using h

theorem shiftedSquare_expansion {n : Nat} (f : BinaryVector n → Int) :
    ((binaryBasis n).map f).sum * ((binaryBasis n).map f).sum =
      ((binaryBasis n).map (fun x => ((binaryBasis n).map (fun u => f x * f (binaryShift x u))).sum)).sum := by
  rw [integerSquare_doubleSum]
  exact binaryShift_doubleSum (fun x y => f x * f y)


theorem walshWireParity_shift {n : Nat} (xs : List (Fin n)) (l u v : BinaryVector n) :
    walshWireParity xs l (binaryShift u v) = Bool.xor (walshWireParity xs l u) (walshWireParity xs l v) := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    simp only [walshWireParity, binaryShift, ih]
    cases l i <;> cases u i <;> cases v i <;>
      cases walshWireParity rest l u <;> cases walshWireParity rest l v <;> rfl

def phasePolarFunction {n : Nat} (q : BinaryVector n → Bool) (x u : BinaryVector n) : Bool :=
  Bool.xor (q (binaryShift x u)) (Bool.xor (q x) (Bool.xor (q u) (q (fun _ => false))))

def functionWalshSum {n : Nat} (q : BinaryVector n → Bool) (l : BinaryVector n) : Int :=
  ((binaryBasis n).map (fun x => integerWalshSign
    (Bool.xor (q x) (walshWireParity (List.finRange n) l x)))).sum

theorem walshSquare_polar_expansion {n : Nat} (q : BinaryVector n → Bool) (l : BinaryVector n) :
    functionWalshSum q l * functionWalshSum q l =
      ((binaryBasis n).map (fun x => ((binaryBasis n).map (fun u =>
        integerWalshSign (Bool.xor (q u) (Bool.xor (q (fun _ => false))
          (walshWireParity (List.finRange n) l u))) *
        integerWalshSign (phasePolarFunction q x u))).sum)).sum := by
  unfold functionWalshSum
  rw [shiftedSquare_expansion]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  simp only [walshWireParity_shift, phasePolarFunction]
  cases q x <;> cases q u <;> cases q (fun _ => false) <;>
    cases q (binaryShift x u) <;> cases walshWireParity (List.finRange n) l x <;>
    cases walshWireParity (List.finRange n) l u <;> rfl

end SectorSimulation
