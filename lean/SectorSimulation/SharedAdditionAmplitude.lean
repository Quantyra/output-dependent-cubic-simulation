import SectorSimulation.ToffoliScaledBasis
namespace SectorSimulation

theorem sharedAddSame_amplitude {n : Nat} (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) (x : BinaryVector n) :
    sharedAmplitude (sharedAddSame a b) x = exactAdd (sharedAmplitude a x) (sharedAmplitude b x) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      change exactOfDyadic _ = exactAdd (exactOfDyadic _) (exactOfDyadic _)
      rw [exact_add_representatives]
      apply Quotient.sound
      change dyadicEquivalent _ _
      cases ha : an x
      cases hb : bn x
      simp only [sharedAddSame, dyadicEquivalent, dyadicAdd, cycloAdd, cycloScale,
        Int.pow_add, Int.mul_add, Int.mul_assoc]

theorem replayExactNative_equal_exponents {n : Nat} (gates : List NativeGate)
    (a b ra rb : SharedDyadicState n) (h : a.exponent = b.exponent)
    (ha : replayExactNative n gates a = some ra) (hb : replayExactNative n gates b = some rb) :
    ra.exponent = rb.exponent := by
  induction gates generalizing a b with
  | nil => simp [replayExactNative] at ha hb; subst ra; subst rb; exact h
  | cons gate rest ih =>
    cases hga : applyExactNative n gate a with
    | none => simp [replayExactNative, hga] at ha
    | some na =>
      cases hgb : applyExactNative n gate b with
      | none => simp [replayExactNative, hgb] at hb
      | some nb =>
        have hn : na.exponent = nb.exponent := by
          rw [applyExactNative_exponent gate a na hga, applyExactNative_exponent gate b nb hgb, h]
        have hia : replayExactNative n rest na = some ra := by simpa [replayExactNative, hga] using ha
        have hib : replayExactNative n rest nb = some rb := by simpa [replayExactNative, hgb] using hb
        exact ih na nb hn hia hib

theorem replayExactNative_add_amplitude {n : Nat} (gates : List NativeGate)
    (a b ra rb : SharedDyadicState n) (h : a.exponent = b.exponent)
    (ha : replayExactNative n gates a = some ra) (hb : replayExactNative n gates b = some rb)
    (x : BinaryVector n) :
    replayExactNative n gates (sharedAddSame a b) = some (sharedAddSame ra rb) ∧
      sharedAmplitude (sharedAddSame ra rb) x = exactAdd (sharedAmplitude ra x) (sharedAmplitude rb x) := by
  refine ⟨?_, sharedAddSame_amplitude ra rb (replayExactNative_equal_exponents gates a b ra rb h ha hb) x⟩
  rw [replayExactNative_add gates a b h, ha, hb]
  rfl

end SectorSimulation
