import SectorSimulation.FourierNormalization

namespace SectorSimulation

def booleanListSum {α : Type} (xs : List α) (f : α → Bool) : Bool :=
  xs.foldr (fun x acc => Bool.xor (f x) acc) false

theorem booleanListSum_xor {α : Type} (xs : List α) (f g : α → Bool) :
    booleanListSum xs (fun x => Bool.xor (f x) (g x)) =
      Bool.xor (booleanListSum xs f) (booleanListSum xs g) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [booleanListSum, List.foldr_cons] at ih ⊢
    rw [ih]
    cases f a <;> cases g a <;>
      cases rest.foldr (fun x acc => Bool.xor (f x) acc) false <;>
      cases rest.foldr (fun x acc => Bool.xor (g x) acc) false <;> rfl

theorem booleanListSum_and {α : Type} (xs : List α) (f : α → Bool) (b : Bool) :
    Bool.and b (booleanListSum xs f) = booleanListSum xs (fun x => Bool.and b (f x)) := by
  cases b with
  | false => induction xs <;> simp_all [booleanListSum]
  | true => simp

theorem booleanListSum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Bool) :
    booleanListSum xs (fun x => booleanListSum ys (f x)) =
      booleanListSum ys (fun y => booleanListSum xs (fun x => f x y)) := by
  induction xs with
  | nil => induction ys <;> simp_all [booleanListSum]
  | cons x rest ih =>
    simp only [booleanListSum, List.foldr_cons]
    change Bool.xor (booleanListSum ys (f x))
      (booleanListSum rest (fun x => booleanListSum ys (f x))) =
      booleanListSum ys (fun y => Bool.xor (f x y) (booleanListSum rest (fun x => f x y)))
    rw [booleanListSum_xor, ih]

theorem walshWireParity_as_sum {n : Nat} (xs : List (Fin n)) (l x : BinaryVector n) :
    walshWireParity xs l x = booleanListSum xs (fun i => l i && x i) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [walshWireParity, booleanListSum, ih]

theorem xorFoldl_as_sum {α : Type} (xs : List α) (f : α → Bool) (c : Bool) :
    xs.foldl (fun acc x => Bool.xor acc (f x)) c = Bool.xor c (booleanListSum xs f) := by
  induction xs generalizing c with
  | nil => cases c <;> rfl
  | cons a rest ih =>
    simp only [List.foldl_cons, booleanListSum, List.foldr_cons]
    rw [ih]
    change Bool.xor (Bool.xor c (f a)) (booleanListSum rest f) = Bool.xor c (Bool.xor (f a) (booleanListSum rest f))
    exact Bool.xor_assoc _ _ _

def transposeBinaryMatrix {n : Nat} (J : BinaryMatrix n) : BinaryMatrix n := fun i j => J j i

theorem binaryTranspose_character {n : Nat} (J : BinaryMatrix n) (l x : BinaryVector n) :
    walshWireParity (List.finRange n) l (matrixApply J x) =
      walshWireParity (List.finRange n) (matrixApply (transposeBinaryMatrix J) l) x := by
  simp only [walshWireParity_as_sum, matrixApply, transposeBinaryMatrix, xorFoldl_as_sum, Bool.false_xor]
  calc
    booleanListSum (List.finRange n) (fun i => l i && booleanListSum (List.finRange n) (fun j => J i j && x j)) =
        booleanListSum (List.finRange n) (fun i => booleanListSum (List.finRange n) (fun j => l i && (J i j && x j))) := by
      simp only [booleanListSum_and]
    _ = booleanListSum (List.finRange n) (fun j => booleanListSum (List.finRange n) (fun i => l i && (J i j && x j))) :=
      booleanListSum_swap _ _ _
    _ = booleanListSum (List.finRange n) (fun j => booleanListSum (List.finRange n) (fun i => J i j && l i) && x j) := by
      apply congrArg (booleanListSum (List.finRange n))
      funext j
      rw [Bool.and_comm, booleanListSum_and]
      apply congrArg (booleanListSum (List.finRange n))
      funext i
      cases l i <;> cases J i j <;> cases x j <;> rfl


end SectorSimulation
