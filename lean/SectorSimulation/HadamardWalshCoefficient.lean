import SectorSimulation.HadamardPathEndpoint
namespace SectorSimulation

def walshWireParity {n : Nat} : List (Fin n) → BinaryVector n → BinaryVector n → Bool
  | [], _, _ => false
  | wire :: rest, basis, x => Bool.xor (basis wire && x wire) (walshWireParity rest basis x)

def iterateHadamardScale : Nat → ExactAmplitude → ExactAmplitude
  | 0, c => c
  | k + 1, c => iterateHadamardScale k (exactMul exactHadamardScale c)

def exactSigned (negative : Bool) (c : ExactAmplitude) : ExactAmplitude :=
  if negative then exactNeg c else c

theorem exactNeg_involutive (a : ExactAmplitude) : exactNeg (exactNeg a) = a := by
  induction a using Quotient.ind with
  | _ a =>
    change exactOfDyadic (dyadicNeg (dyadicNeg a)) = exactOfDyadic a
    congr 1
    cases a with | mk an ae =>
      cases an
      simp [dyadicNeg, cycloNeg]

theorem iterateHadamardScale_neg (k : Nat) (c : ExactAmplitude) :
    iterateHadamardScale k (exactNeg c) = exactNeg (iterateHadamardScale k c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [iterateHadamardScale, exactMul_neg]
    exact ih _

theorem walshWireParity_flip_outside {n : Nat} (wires : List (Fin n))
    (wire : Fin n) (basis x : BinaryVector n) (h : wire ∉ wires) :
    walshWireParity wires (flipWire wire basis) x = walshWireParity wires basis x := by
  induction wires with
  | nil => rfl
  | cons a rest ih =>
    have hne : a ≠ wire := by intro he; apply h; simp [he]
    have hr : wire ∉ rest := by intro hm; exact h (by simp [hm])
    simp [walshWireParity, flipWire, hne, ih hr]

theorem selectedPathCoefficient_walsh {n : Nat} (wires : List (Fin n))
    (c : ExactAmplitude) (basis x : BinaryVector n) (hn : wires.Nodup) :
    selectedPathCoefficient wires c basis x =
      exactSigned (walshWireParity wires basis x) (iterateHadamardScale wires.length c) := by
  induction wires generalizing c basis with
  | nil => rfl
  | cons wire rest ih =>
    have hs := List.nodup_cons.mp hn
    have hp := walshWireParity_flip_outside rest wire basis x hs.1
    cases hb : basis wire <;> cases hx : x wire <;>
      simp [selectedPathCoefficient, walshWireParity, iterateHadamardScale, exactSigned,
        hb, hx, ih _ _ hs.2, hp, iterateHadamardScale_neg, exactNeg_involutive]
    cases hpar : walshWireParity rest basis x <;> simp [hpar]


/-- Closed exact Walsh-character sum for the all-wire Hadamard kernel. -/
theorem hadamardKernel_allWire_walsh_sum {n : Nat}
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel (List.finRange n) f x =
      (binaryBasis n).foldr (fun basis acc => exactAdd
        (exactSigned (walshWireParity (List.finRange n) basis x)
          (iterateHadamardScale n (f basis))) acc) exactZero := by
  have h := hadamardKernel_allWire_coefficient_sum f x
  simpa only [selectedPathCoefficient_walsh _ _ _ _ (List.nodup_finRange n), List.length_finRange] using h

theorem nativePythonFourier_walsh_sum {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result x =
        (binaryBasis n).foldr (fun basis acc => exactAdd
          (exactSigned (walshWireParity (List.finRange n) basis x)
            (iterateHadamardScale n (sharedAmplitude state (runCNOTs (rowProgramCNOTs ops) basis)))) acc) exactZero := by
  obtain ⟨result, hr, hf⟩ := hadamardKernel_nativePythonFourier J ops hp state
  refine ⟨result, hr, ?_⟩
  intro x
  rw [hf x, hadamardKernel_allWire_walsh_sum]

end SectorSimulation
