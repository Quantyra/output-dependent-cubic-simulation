import SectorSimulation.MatrixPairing
namespace SectorSimulation

theorem exactOne_mul (a : ExactAmplitude) : exactMul exactOne a = a := by
  induction a using Quotient.ind with
  | _ a =>
    change exactOfDyadic (dyadicMultiply dyadicOne a) = exactOfDyadic a
    cases a with
    | mk num exp =>
      simp only [dyadicMultiply, dyadicOne, Nat.zero_add]
      apply congrArg exactOfDyadic
      apply congrArg (fun z : Cyclo8 => DyadicCyclo.mk z exp)
      cases num
      change cycloMul cycloOne _ = _
      simp [cycloMul, cycloOne]

theorem iterateHadamardScale_factor (k : Nat) (a : ExactAmplitude) :
    iterateHadamardScale k a = exactMul (iterateHadamardScale k exactOne) a := by
  induction k generalizing a with
  | zero => simp [iterateHadamardScale, exactOne_mul]
  | succ k ih =>
    simp only [iterateHadamardScale]
    rw [ih (exactMul exactHadamardScale a), ih (exactMul exactHadamardScale exactOne), exactMul_comm exactHadamardScale exactOne, exactOne_mul]
    rw [exactMul_assoc]

theorem hadamardScale_double_square (a : ExactAmplitude) :
    exactAdd (exactMul exactHadamardScale (exactMul exactHadamardScale a))
      (exactMul exactHadamardScale (exactMul exactHadamardScale a)) = a := by
  rw [← exactMul_assoc, ← exactAdd_mul,
    exact_hadamard_scalar_normalization, exactOne_mul]

theorem iterateHadamardScale_double_square (k : Nat) (a : ExactAmplitude) :
    exactAdd (iterateHadamardScale (k+2) a) (iterateHadamardScale (k+2) a) =
      iterateHadamardScale k a := by
  simp only [iterateHadamardScale]
  rw [iterateHadamardScale_factor k (exactMul exactHadamardScale (exactMul exactHadamardScale a)),
    iterateHadamardScale_factor k a, ← exactMul_add, hadamardScale_double_square]


theorem exactFoldr_mul {α : Type} (xs : List α) (f : α → ExactAmplitude)
    (c : ExactAmplitude) :
    xs.foldr (fun a acc => exactAdd (exactMul c (f a)) acc) exactZero =
      exactMul c (xs.foldr (fun a acc => exactAdd (f a) acc) exactZero) := by
  induction xs with
  | nil => simp [exactMul_zero]
  | cons a rest ih => simp only [List.foldr_cons, ih, exactMul_add]

theorem exactSigned_mul (b : Bool) (c a : ExactAmplitude) :
    exactSigned b (exactMul c a) = exactMul c (exactSigned b a) := by
  cases b <;> simp [exactSigned, exactMul_neg]

theorem nativePythonFourier_normalized_sum {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result x = exactMul (iterateHadamardScale n exactOne)
        ((binaryBasis n).foldr (fun y acc => exactAdd
          (exactSigned (matrixPairingParity J x y) (sharedAmplitude state y)) acc) exactZero) := by
  obtain ⟨result, hr, hf⟩ := nativePythonFourier_pairing_sum J ops hp state
  refine ⟨result, hr, ?_⟩
  intro x
  rw [hf x]
  rw [← exactFoldr_mul]
  congr 1
  funext y acc
  rw [iterateHadamardScale_factor n (sharedAmplitude state y), exactSigned_mul]

end SectorSimulation
