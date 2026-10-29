import SectorSimulation.ThreeWireSlice
namespace SectorSimulation

inductive ThreeWireGate where
  | hadamard (i : Fin 3)
  | x (i : Fin 3)
  | z (i : Fin 3)
  | t (i : Fin 3) (inverse : Bool)
  | cnot (control target : Fin 3)

def runThreeWireGate {n : Nat} (w : Fin 3 → Fin n) (gate : ThreeWireGate)
    (state : SharedDyadicState n) : SharedDyadicState n :=
  match gate with
  | .hadamard i => sharedHadamard (w i) state
  | .x i => sharedX (w i) state
  | .z i => sharedZ (w i) state
  | .t i inverse => sharedT (w i) inverse state
  | .cnot control target => sharedCNOT (w control) (w target) state

def runThreeWireProgram {n : Nat} (w : Fin 3 → Fin n) : List ThreeWireGate → SharedDyadicState n → SharedDyadicState n
  | [], state => state
  | gate :: rest, state => runThreeWireProgram w rest (runThreeWireGate w gate state)

theorem sliceThree_gate {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (gate : ThreeWireGate) (state : SharedDyadicState n) :
    sliceThree w base (runThreeWireGate w gate state) = runThreeWireGate id gate (sliceThree w base state) := by
  cases gate <;> simp [runThreeWireGate, sliceThree_hadamard w hw, sliceThree_x w hw,
    sliceThree_z w hw, sliceThree_t w hw, sliceThree_cnot w hw]

theorem sliceThree_program {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (gates : List ThreeWireGate) (state : SharedDyadicState n) :
    sliceThree w base (runThreeWireProgram w gates state) =
      runThreeWireProgram id gates (sliceThree w base state) := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    simp only [runThreeWireProgram]
    rw [ih, sliceThree_gate w hw]

def threeWireToffoli : List ThreeWireGate :=
  [.hadamard 2, .cnot 1 2, .t 2 true, .cnot 0 2, .t 2 false, .cnot 1 2,
   .t 2 true, .cnot 0 2, .t 1 false, .t 2 false, .hadamard 2, .cnot 0 1,
   .t 0 false, .t 1 true, .cnot 0 1]

theorem threeWireToffoli_native (state : SharedDyadicState 3) :
    replayExactNative 3 nativeToffoli012 state = some (runThreeWireProgram id threeWireToffoli state) := by
  simp [nativeToffoli012, threeWireToffoli, replayExactNative, applyExactNative,
    runThreeWireProgram, runThreeWireGate]

theorem threeWireToffoli_slice {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) :
    replayExactNative 3 nativeToffoli012 (sliceThree w base state) =
      some (sliceThree w base (runThreeWireProgram w threeWireToffoli state)) := by
  rw [threeWireToffoli_native, sliceThree_program w hw]

theorem embedThree_recover {n : Nat} (w : Fin 3 → Fin n) (base : BinaryVector n) :
    embedThree w base (fun i => base (w i)) = base := by
  funext j
  simp only [embedThree]
  by_cases h0 : j = w 0 <;> by_cases h1 : j = w 1 <;> by_cases h2 : j = w 2 <;> simp_all

theorem embedThree_toffoli {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (bits : BinaryVector 3) :
    embedThree w base (applyToffoli 0 1 2 bits) =
      applyToffoli (w 0) (w 1) (w 2) (embedThree w base bits) := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;>
    simp [applyToffoli, embedThree_at w hw, embedThree_flip w hw, h0, h1]

theorem sliceThree_toffoli {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (base : BinaryVector n) (state : SharedDyadicState n) :
    sliceThree w base (sharedToffoli (w 0) (w 1) (w 2) state) =
      sharedToffoli 0 1 2 (sliceThree w base state) := by
  cases state with | mk f e =>
    simp [sliceThree, sharedToffoli, embedThree_toffoli w hw]

theorem threeWireToffoli_global_correct {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (runThreeWireProgram w threeWireToffoli state) x =
      sharedAmplitude (sharedToffoli (w 0) (w 1) (w 2) state) x := by
  let bits : BinaryVector 3 := fun i => x (w i)
  obtain ⟨result, hr, ha⟩ := toffoli_threeBit_all_amplitudes (sliceThree w x state)
  have hs := threeWireToffoli_slice w hw x state
  rw [hr] at hs
  have heq : result = sliceThree w x (runThreeWireProgram w threeWireToffoli state) := Option.some.inj hs
  have hh := ha bits
  rw [heq, ← sliceThree_toffoli w hw] at hh
  simpa [sharedAmplitude, sliceThree, bits, embedThree_recover] using hh

end SectorSimulation
