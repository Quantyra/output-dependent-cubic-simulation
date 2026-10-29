import SectorSimulation.HadamardFiniteSums
import SectorSimulation.ExhaustiveMatrixSolve
namespace SectorSimulation

instance binaryVectorDecidableEq (n : Nat) : DecidableEq (BinaryVector n) :=
  fun a b => decidable_of_iff (vectorEqual a b = true) (vectorEqual_correct a b)

def uniqueList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest => if a ∈ uniqueList rest then uniqueList rest else a :: uniqueList rest

theorem uniqueList_mem {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ uniqueList xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [uniqueList]
  | cons b rest ih =>
    simp only [uniqueList]
    split <;> simp_all

theorem uniqueList_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (uniqueList xs).Nodup := by
  induction xs with
  | nil => simp [uniqueList]
  | cons b rest ih =>
    simp only [uniqueList]
    split <;> simp_all

def binaryBasis (n : Nat) : List (BinaryVector n) := uniqueList (allVectors n)

theorem binaryBasis_complete {n : Nat} (x : BinaryVector n) : x ∈ binaryBasis n := by
  exact (uniqueList_mem x (allVectors n)).mpr (allVectors_complete x)

theorem binaryBasis_nodup (n : Nat) : (binaryBasis n).Nodup := uniqueList_nodup (allVectors n)

def basisTerm {n : Nat} (f : BinaryVector n → ExactAmplitude)
    (basis x : BinaryVector n) : ExactAmplitude := if x = basis then f basis else exactZero

theorem exactZero_add (a : ExactAmplitude) : exactAdd exactZero a = a := by
  rw [exactAdd_comm, exactAdd_zero]

theorem basisSum_absent {n : Nat} (xs : List (BinaryVector n))
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) (h : x ∉ xs) :
    exactFunctionSum xs (basisTerm f) x = exactZero := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hn : x ≠ a := by intro he; subst a; exact h (by simp)
    have hr : x ∉ rest := by intro hm; exact h (by simp [hm])
    change exactAdd (basisTerm f a x) (exactFunctionSum rest (basisTerm f) x) = _
    simp [basisTerm, hn, ih hr, exactAdd_zero]

theorem basisSum_present {n : Nat} (xs : List (BinaryVector n))
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n)
    (hn : xs.Nodup) (hm : x ∈ xs) : exactFunctionSum xs (basisTerm f) x = f x := by
  induction xs with
  | nil => simp at hm
  | cons a rest ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : x = a
    · subst a
      change exactAdd (basisTerm f x x) (exactFunctionSum rest (basisTerm f) x) = _
      simp [basisTerm, basisSum_absent rest f x hn'.1, exactAdd_zero]
    · have hr : x ∈ rest := by simpa [he] using hm
      change exactAdd (basisTerm f a x) (exactFunctionSum rest (basisTerm f) x) = _
      simp [basisTerm, he, exactZero_add, ih hn'.2 hr]

theorem binaryBasis_expansion {n : Nat} (f : BinaryVector n → ExactAmplitude) :
    exactFunctionSum (binaryBasis n) (basisTerm f) = f := by
  funext x
  exact basisSum_present (binaryBasis n) f x (binaryBasis_nodup n) (binaryBasis_complete x)

theorem hadamardKernel_basisExpansion {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel wires f x =
      (binaryBasis n).foldr (fun a acc => exactAdd (hadamardKernel wires (basisTerm f a) x) acc) exactZero := by
  calc
    hadamardKernel wires f x = hadamardKernel wires (exactFunctionSum (binaryBasis n) (basisTerm f)) x :=
      congrArg (fun g => hadamardKernel wires g x) (binaryBasis_expansion f).symm
    _ = _ := hadamardKernel_sum wires (binaryBasis n) (basisTerm f) x

end SectorSimulation
