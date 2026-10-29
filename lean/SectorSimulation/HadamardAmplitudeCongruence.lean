import SectorSimulation.MappedNativeToffoli
namespace SectorSimulation

def sharedSubSame {n : Nat} (a b : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => cycloSub (a.numerator x) (b.numerator x), a.exponent⟩

theorem sharedSubSame_amplitude {n : Nat} (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) (x : BinaryVector n) :
    sharedAmplitude (sharedSubSame a b) x = exactSub (sharedAmplitude a x) (sharedAmplitude b x) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      change exactOfDyadic _ = exactSub (exactOfDyadic _) (exactOfDyadic _)
      apply Quotient.sound
      change dyadicEquivalent _ _
      cases ha : an x
      cases hb : bn x
      simp only [sharedSubSame, dyadicEquivalent, dyadicSubtract, cycloSub, cycloScale,
        Int.pow_add, Int.mul_sub, Int.mul_assoc]

theorem sharedHadamard_amplitude {n : Nat} (wire : Fin n) (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard wire state) x =
      exactMul exactHadamardScale (if x wire then
        exactSub (sharedAmplitude state (flipWire wire x)) (sharedAmplitude state x)
        else exactAdd (sharedAmplitude state x) (sharedAmplitude state (flipWire wire x))) := by
  cases hx : x wire
  · have he : (sharedX wire state).exponent = state.exponent := rfl
    have hs := sharedShiftScale_amplitude cycloSqrtTwo 1 (sharedAddSame state (sharedX wire state)) x
    rw [sharedAddSame_amplitude state (sharedX wire state) he.symm x] at hs
    simpa [sharedHadamard, cycloHadamardNumerator, sharedShift, sharedScale, sharedAddSame,
      sharedX, sharedAmplitude, exactHadamardScale, dyadicHadamardScale, hx] using hs
  · have he : (sharedX wire state).exponent = state.exponent := rfl
    have hs := sharedShiftScale_amplitude cycloSqrtTwo 1 (sharedSubSame (sharedX wire state) state) x
    rw [sharedSubSame_amplitude (sharedX wire state) state he x] at hs
    simpa [sharedHadamard, cycloHadamardNumerator, sharedShift, sharedScale, sharedSubSame,
      sharedX, sharedAmplitude, exactHadamardScale, dyadicHadamardScale, hx] using hs

theorem sharedHadamard_amplitude_congr {n : Nat} (wire : Fin n) (a b : SharedDyadicState n)
    (h : ∀ x, sharedAmplitude a x = sharedAmplitude b x) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard wire a) x = sharedAmplitude (sharedHadamard wire b) x := by
  rw [sharedHadamard_amplitude, sharedHadamard_amplitude, h x, h (flipWire wire x)]

theorem mappedToffoli_cubic_sign {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedHadamard (w 2)
      (runThreeWireProgram w threeWireToffoli (sharedHadamard (w 2) state))) x =
      sharedAmplitude (sharedCubicSign (w 0) (w 1) (w 2) state) x := by
  have h0 : w 0 ≠ w 2 := by intro he; exact (by decide : (0 : Fin 3) ≠ 2) (hw he)
  have h1 : w 1 ≠ w 2 := by intro he; exact (by decide : (1 : Fin 3) ≠ 2) (hw he)
  have h : ∀ y, sharedAmplitude (runThreeWireProgram w threeWireToffoli (sharedHadamard (w 2) state)) y =
      sharedAmplitude (sharedToffoli (w 0) (w 1) (w 2) (sharedHadamard (w 2) state)) y :=
    threeWireToffoli_global_correct w hw (sharedHadamard (w 2) state)
  exact (sharedHadamard_amplitude_congr (w 2) _ _ h x).trans
    (sharedHToffoliH_cubic_sign (w 0) (w 1) (w 2) h0 h1 state x)

end SectorSimulation
