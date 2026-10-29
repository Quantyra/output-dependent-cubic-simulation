import SectorSimulation.DerivativeSize
namespace SectorSimulation

def vectorXor {n : Nat} (x y : BinaryVector n) : BinaryVector n := fun i => Bool.xor (x i) (y i)
def zeroVector {n : Nat} : BinaryVector n := fun _ => false

theorem matrixFold_xor {n : Nat} (row : Fin n → Bool) (x y : BinaryVector n)
    (indices : List (Fin n)) (a b : Bool) :
    indices.foldl (fun acc i => Bool.xor acc (row i && Bool.xor (x i) (y i))) (Bool.xor a b) =
      Bool.xor (indices.foldl (fun acc i => Bool.xor acc (row i && x i)) a)
        (indices.foldl (fun acc i => Bool.xor acc (row i && y i)) b) := by
  induction indices generalizing a b with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    have h : Bool.xor (Bool.xor a b) (row i && Bool.xor (x i) (y i)) =
        Bool.xor (Bool.xor a (row i && x i)) (Bool.xor b (row i && y i)) := by
      cases a <;> cases b <;> cases row i <;> cases x i <;> cases y i <;> simp
    rw [h]
    exact ih _ _

theorem matrixApply_xor {n : Nat} (J : BinaryMatrix n) (x y : BinaryVector n) :
    matrixApply J (vectorXor x y) = vectorXor (matrixApply J x) (matrixApply J y) := by
  funext i
  exact matrixFold_xor (J i) x y (List.finRange n) false false

theorem matrixApply_zero {n : Nat} (J : BinaryMatrix n) : matrixApply J zeroVector = zeroVector := by
  have h := matrixApply_xor J zeroVector zeroVector
  have z : vectorXor (zeroVector : BinaryVector n) zeroVector = zeroVector := by funext i; rfl
  rw [z] at h
  funext i
  have hi := congrFun h i
  cases hval : matrixApply J zeroVector i <;> simp [vectorXor, hval, zeroVector] at hi ⊢

end SectorSimulation
