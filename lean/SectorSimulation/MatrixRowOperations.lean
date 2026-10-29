import SectorSimulation.SourceOutputDerivative
namespace SectorSimulation

def rowSwap {n : Nat} (J : BinaryMatrix n) (a b : Fin n) : BinaryMatrix n :=
  fun i k => if i = a then J b k else if i = b then J a k else J i k

def vectorSwap {n : Nat} (y : BinaryVector n) (a b : Fin n) : BinaryVector n :=
  fun i => if i = a then y b else if i = b then y a else y i

theorem rowSwap_equation {n : Nat} (J : BinaryMatrix n) (x : BinaryVector n) (a b : Fin n) :
    matrixApply (rowSwap J a b) x = vectorSwap (matrixApply J x) a b := by
  funext i
  by_cases ha : i = a
  · simp [matrixApply, rowSwap, vectorSwap, ha]
  · by_cases hb : i = b
    · subst i; have hba : b ≠ a := ha; simp [matrixApply, rowSwap, vectorSwap, hba]
    · simp [matrixApply, rowSwap, vectorSwap, ha, hb]

theorem rowSwap_involutive {n : Nat} (y : BinaryVector n) (a b : Fin n) :
    vectorSwap (vectorSwap y a b) a b = y := by
  funext i
  by_cases hab : a = b
  · subst b; by_cases h : i = a <;> simp [vectorSwap, h]
  · by_cases ha : i = a
    · subst i; simp [vectorSwap, Ne.symm hab]
    · by_cases hb : i = b
      · subst i; simp [vectorSwap, Ne.symm hab]
      · simp [vectorSwap, ha, hb]

theorem rowSwap_preserves_solutions {n : Nat} (J : BinaryMatrix n) (x y : BinaryVector n) (a b : Fin n) :
    matrixApply (rowSwap J a b) x = vectorSwap y a b ↔ matrixApply J x = y := by
  rw [rowSwap_equation]
  constructor
  · intro h
    have h2 := congrArg (fun v => vectorSwap v a b) h
    simpa [rowSwap_involutive] using h2
  · intro h; exact congrArg (fun v => vectorSwap v a b) h

def rowAdd {n : Nat} (J : BinaryMatrix n) (a b : Fin n) : BinaryMatrix n :=
  fun i k => if i = a then Bool.xor (J a k) (J b k) else J i k

def vectorAddRow {n : Nat} (y : BinaryVector n) (a b : Fin n) : BinaryVector n :=
  fun i => if i = a then Bool.xor (y a) (y b) else y i

theorem rowAdd_equation {n : Nat} (J : BinaryMatrix n) (x : BinaryVector n) (a b : Fin n) :
    matrixApply (rowAdd J a b) x = vectorAddRow (matrixApply J x) a b := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [matrixApply, rowAdd, vectorAddRow]
    simpa only [Bool.and_comm] using matrixFold_xor x (J a) (J b) (List.finRange n) false false
  · simp [matrixApply, rowAdd, vectorAddRow, hi]

theorem vectorAddRow_involutive {n : Nat} (y : BinaryVector n) (a b : Fin n) (hab : a ≠ b) :
    vectorAddRow (vectorAddRow y a b) a b = y := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [vectorAddRow, if_neg (Ne.symm hab)]
    cases y a <;> cases y b <;> rfl
  · simp [vectorAddRow, hi]

theorem rowAdd_preserves_solutions {n : Nat} (J : BinaryMatrix n) (x y : BinaryVector n)
    (a b : Fin n) (hab : a ≠ b) :
    matrixApply (rowAdd J a b) x = vectorAddRow y a b ↔ matrixApply J x = y := by
  rw [rowAdd_equation]
  constructor
  · intro h
    have h2 := congrArg (fun v => vectorAddRow v a b) h
    simpa [vectorAddRow_involutive, hab] using h2
  · intro h; exact congrArg (fun v => vectorAddRow v a b) h

end SectorSimulation
