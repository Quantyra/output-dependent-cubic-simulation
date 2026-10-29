import SectorSimulation.ModeledFourier
namespace SectorSimulation

/-- Exact one-wire Fourier update, on arbitrary exact amplitude functions. -/
def hadamardKernelStep {n : Nat} (wire : Fin n)
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) : ExactAmplitude :=
  exactMul exactHadamardScale (if x wire then exactSub (f (flipWire wire x)) (f x)
    else exactAdd (f x) (f (flipWire wire x)))

/-- Iterate the explicit two-branch normalized Hadamard kernel in native gate order. -/
def hadamardKernel {n : Nat} : List (Fin n) → (BinaryVector n → ExactAmplitude) →
    BinaryVector n → ExactAmplitude
  | [], f => f
  | wire :: rest, f => hadamardKernel rest (hadamardKernelStep wire f)


/-- Every Hadamard adds exactly one power of two to the shared denominator. -/
theorem runSharedHadamards_exponent {n : Nat} (wires : List (Fin n))
    (state : SharedDyadicState n) :
    (runSharedHadamards wires state).exponent = state.exponent + wires.length := by
  induction wires generalizing state with
  | nil => simp [runSharedHadamards]
  | cons wire rest ih =>
    simp [runSharedHadamards, ih, sharedHadamard, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem hadamardKernel_run {n : Nat} (wires : List (Fin n)) (state : SharedDyadicState n)
    (x : BinaryVector n) :
    sharedAmplitude (runSharedHadamards wires state) x =
      hadamardKernel wires (sharedAmplitude state) x := by
  induction wires generalizing state with
  | nil => rfl
  | cons wire rest ih =>
    simp only [runSharedHadamards, hadamardKernel]
    rw [ih]
    have hf : sharedAmplitude (sharedHadamard wire state) = hadamardKernelStep wire (sharedAmplitude state) := by
      funext y
      exact sharedHadamard_amplitude wire state y
    rw [hf]

theorem hadamardKernel_pythonFourier {n : Nat} (ops : List (RowOperation n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (modeledFourier ops state) x =
      hadamardKernel (List.finRange n)
        (fun y => sharedAmplitude state (runCNOTs (rowProgramCNOTs ops) y)) x := by
  unfold modeledFourier
  rw [hadamardKernel_run]
  have hf : sharedAmplitude (runSharedCNOTs (rowProgramCNOTs ops).reverse state) =
      (fun y => sharedAmplitude state (runCNOTs (rowProgramCNOTs ops) y)) := by
    funext y
    simpa using sharedCNOTs_amplitude (rowProgramCNOTs ops).reverse state y
  rw [hf]

theorem hadamardKernel_nativePythonFourier {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result x =
        hadamardKernel (List.finRange n)
          (fun y => sharedAmplitude state (runCNOTs (rowProgramCNOTs ops) y)) x := by
  exact ⟨modeledFourier ops state, exactNativeFourier_program J ops hp state,
    hadamardKernel_pythonFourier ops state⟩

end SectorSimulation
