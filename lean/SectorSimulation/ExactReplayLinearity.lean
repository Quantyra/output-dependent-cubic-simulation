import SectorSimulation.ExactGateLinearity
namespace SectorSimulation

def nativeHadamardCount (gate : NativeGate) : Nat := if gate.tag == "H" then 1 else 0

theorem applyExactNative_exponent {n : Nat} (gate : NativeGate) (a result : SharedDyadicState n)
    (h : applyExactNative n gate a = some result) :
    result.exponent = a.exponent + nativeHadamardCount gate := by
  unfold applyExactNative at h
  repeat' split at h <;> simp_all [nativeHadamardCount, sharedHadamard, sharedX, sharedZ, sharedT, sharedCNOT] <;> grind

theorem applyExactNative_add {n : Nat} (gate : NativeGate) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    applyExactNative n gate (sharedAddSame a b) =
      (applyExactNative n gate a).bind (fun ra =>
        (applyExactNative n gate b).map (fun rb => sharedAddSame ra rb)) := by
  unfold applyExactNative
  repeat' split <;> simp_all [sharedHadamard_add, sharedX_add, sharedZ_add, sharedT_add, sharedCNOT_add]
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all

theorem replayExactNative_add {n : Nat} (gates : List NativeGate) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    replayExactNative n gates (sharedAddSame a b) =
      (replayExactNative n gates a).bind (fun ra =>
        (replayExactNative n gates b).map (fun rb => sharedAddSame ra rb)) := by
  induction gates generalizing a b with
  | nil => rfl
  | cons gate rest ih =>
    cases ha : applyExactNative n gate a with
    | none =>
      have hs : applyExactNative n gate (sharedAddSame a b) = none := by
        rw [applyExactNative_add gate a b h, ha]
        rfl
      simp [replayExactNative, ha, hs]
    | some aa =>
      cases hb : applyExactNative n gate b with
      | none =>
        have hs : applyExactNative n gate (sharedAddSame a b) = none := by
          rw [applyExactNative_add gate a b h, ha, hb]
          rfl
        simp [replayExactNative, ha, hb, hs]
      | some bb =>
        have hs : applyExactNative n gate (sharedAddSame a b) = some (sharedAddSame aa bb) := by
          rw [applyExactNative_add gate a b h, ha, hb]
          rfl
        have he : aa.exponent = bb.exponent := by
          rw [applyExactNative_exponent gate a aa ha, applyExactNative_exponent gate b bb hb, h]
        simpa [replayExactNative, ha, hb, hs] using ih aa bb he

end SectorSimulation
