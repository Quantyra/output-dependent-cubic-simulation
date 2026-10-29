import SectorSimulation.HadamardMatrixSum
namespace SectorSimulation

/-- Binary dot products are symmetric, independently of matrix symmetry. -/
theorem walshWireParity_comm {n : Nat} (wires : List (Fin n))
    (x y : BinaryVector n) :
    walshWireParity wires x y = walshWireParity wires y x := by
  induction wires with
  | nil => rfl
  | cons a rest ih => simp [walshWireParity, Bool.and_comm, ih]

/-- The parity of x^T J y used in the manuscript Fourier kernel. -/
def matrixPairingParity {n : Nat} (J : BinaryMatrix n) (x y : BinaryVector n) : Bool :=
  walshWireParity (List.finRange n) x (matrixApply J y)

/-- Exact modeled Fourier replay has the manuscript's matrix pairing sign. -/
theorem nativePythonFourier_pairing_sum {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result x =
        (binaryBasis n).foldr (fun y acc => exactAdd
          (exactSigned (matrixPairingParity J x y)
            (iterateHadamardScale n (sharedAmplitude state y))) acc) exactZero := by
  obtain ⟨result, hr, hf⟩ := nativePythonFourier_matrix_sum J ops hp state
  refine ⟨result, hr, ?_⟩
  intro x
  simpa only [matrixPairingParity, walshWireParity_comm] using hf x

end SectorSimulation
