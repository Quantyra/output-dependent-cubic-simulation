import SectorSimulation.ExactGaussianCNOTReplay
namespace SectorSimulation

def runSharedHadamards {n : Nat} : List (Fin n) → SharedDyadicState n → SharedDyadicState n
  | [], state => state
  | wire :: rest, state => runSharedHadamards rest (sharedHadamard wire state)

def nativeHadamardRecords {n : Nat} (wires : List (Fin n)) : List NativeGate :=
  wires.map (fun wire => ⟨"H", [wire.val]⟩)

theorem exactNativeHadamardProgram {n : Nat} (wires : List (Fin n)) (state : SharedDyadicState n) :
    replayExactNative n (nativeHadamardRecords wires) state = some (runSharedHadamards wires state) := by
  induction wires generalizing state with
  | nil => rfl
  | cons wire rest ih =>
    simpa [nativeHadamardRecords, replayExactNative, applyExactNative, wire.isLt, runSharedHadamards] using
      ih (sharedHadamard wire state)

theorem runSharedHadamards_congr {n : Nat} (wires : List (Fin n)) (a b : SharedDyadicState n)
    (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) :
    ∀ x, sharedAmplitude (runSharedHadamards wires a) x = sharedAmplitude (runSharedHadamards wires b) x := by
  induction wires generalizing a b with
  | nil => exact h
  | cons wire rest ih =>
    apply ih (sharedHadamard wire a) (sharedHadamard wire b)
    exact sharedHadamard_amplitude_congr wire a b h

theorem runSharedHadamards_append {n : Nat} (a b : List (Fin n)) (state : SharedDyadicState n) :
    runSharedHadamards (a ++ b) state = runSharedHadamards b (runSharedHadamards a state) := by
  induction a generalizing state with
  | nil => rfl
  | cons wire rest ih => simpa [runSharedHadamards] using ih (sharedHadamard wire state)

theorem runSharedHadamards_reverse_cancel {n : Nat} (wires : List (Fin n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (runSharedHadamards wires.reverse (runSharedHadamards wires state)) x = sharedAmplitude state x := by
  induction wires generalizing state x with
  | nil => rfl
  | cons wire rest ih =>
    simp only [runSharedHadamards, List.reverse_cons, runSharedHadamards_append]
    have hr : ∀ y, sharedAmplitude (runSharedHadamards rest.reverse
      (runSharedHadamards rest (sharedHadamard wire state))) y = sharedAmplitude (sharedHadamard wire state) y :=
      ih (sharedHadamard wire state)
    exact (sharedHadamard_amplitude_congr wire _ _ hr x).trans (sharedHadamard_squared wire state x)

theorem exactNativeHadamard_reverse_cancel {n : Nat} (wires : List (Fin n))
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (nativeHadamardRecords (wires ++ wires.reverse)) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude state x := by
  refine ⟨runSharedHadamards (wires ++ wires.reverse) state, exactNativeHadamardProgram _ state, ?_⟩
  intro x
  rw [runSharedHadamards_append]
  exact runSharedHadamards_reverse_cancel wires state x

def nativeFourierRecords {n : Nat} (ops : List (RowOperation n)) : List NativeGate :=
  nativeHadamardRecords (List.finRange n) ++ encodeCNOTProgram (rowProgramCNOTs ops).reverse

theorem exactNativeFourier_decomposition {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hprog : gaussianRowProgram J = some ops) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (nativeFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result (matrixApply J x) =
        sharedAmplitude (runSharedHadamards (List.finRange n) state) x := by
  obtain ⟨result, hr, ha⟩ := exactNativeGaussianCNOTs J ops hprog (runSharedHadamards (List.finRange n) state)
  refine ⟨result, ?_, ha⟩
  simp only [nativeFourierRecords, replayExactNative_append, exactNativeHadamardProgram]
  exact hr

end SectorSimulation
