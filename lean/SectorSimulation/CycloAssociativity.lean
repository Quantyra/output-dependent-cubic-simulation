import SectorSimulation.ExactReplayLinearity
namespace SectorSimulation

theorem cyclo_mul_assoc (a b c : Cyclo8) : (a*b)*c = a*(b*c) := by
  change cycloMul (cycloMul a b) c = cycloMul a (cycloMul b c)
  cases a; cases b; cases c
  simp only [cycloMul, Cyclo8.mk.injEq, Int.mul_add, Int.mul_sub, Int.mul_left_comm, Int.mul_comm]
  constructor <;> omega

theorem cyclo_mul_neg_right (a b : Cyclo8) : cycloMul a (cycloNeg b) = cycloNeg (cycloMul a b) := by
  cases a; cases b
  simp only [cycloMul, cycloNeg, Cyclo8.mk.injEq, Int.mul_neg]
  constructor <;> omega

theorem cyclo_mul_central (a b c : Cyclo8) : a*(b*c) = b*(a*c) := by
  rw [← cyclo_mul_assoc, cyclo_mul_comm a b, cyclo_mul_assoc]

def sharedScale {n : Nat} (k : Cyclo8) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => cycloMul k (state.numerator x), state.exponent⟩

theorem sharedHadamard_scale {n : Nat} (wire : Fin n) (k : Cyclo8) (state : SharedDyadicState n) :
    sharedHadamard wire (sharedScale k state) = sharedScale k (sharedHadamard wire state) := by
  cases state with | mk f e =>
    simp only [sharedHadamard, sharedScale]
    congr 1
    funext x
    simp only [cycloHadamardNumerator]
    cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true]
    · change cycloSqrtTwo * (k * f x + k * f (flipWire wire x)) =
        k * (cycloSqrtTwo * (f x + f (flipWire wire x)))
      rw [← cyclo_mul_add]
      exact cyclo_sqrt_two_central k _
    · change cycloSqrtTwo * (k * f (flipWire wire x) - k * f x) =
        k * (cycloSqrtTwo * (f (flipWire wire x) - f x))
      rw [← cyclo_mul_sub]
      exact cyclo_sqrt_two_central k _

theorem sharedCNOT_scale {n : Nat} (control target : Fin n) (k : Cyclo8) (state : SharedDyadicState n) :
    sharedCNOT control target (sharedScale k state) = sharedScale k (sharedCNOT control target state) := by rfl

theorem sharedX_scale {n : Nat} (wire : Fin n) (k : Cyclo8) (state : SharedDyadicState n) :
    sharedX wire (sharedScale k state) = sharedScale k (sharedX wire state) := by rfl

theorem sharedZ_scale {n : Nat} (wire : Fin n) (k : Cyclo8) (state : SharedDyadicState n) :
    sharedZ wire (sharedScale k state) = sharedScale k (sharedZ wire state) := by
  cases state with | mk f e =>
    simp only [sharedZ, sharedScale]
    congr 1
    funext x
    cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true]
    exact (cyclo_mul_neg_right k (f x)).symm

theorem sharedT_scale {n : Nat} (wire : Fin n) (inverse : Bool) (k : Cyclo8) (state : SharedDyadicState n) :
    sharedT wire inverse (sharedScale k state) = sharedScale k (sharedT wire inverse state) := by
  cases state with | mk f e =>
    simp only [sharedT, sharedScale]
    congr 1
    funext x
    cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true]
    exact cyclo_mul_central (if inverse then cycloOmegaInv else cycloOmega) k (f x)

theorem applyExactNative_scale {n : Nat} (gate : NativeGate) (k : Cyclo8) (state : SharedDyadicState n) :
    applyExactNative n gate (sharedScale k state) =
      (applyExactNative n gate state).map (sharedScale k) := by
  unfold applyExactNative
  repeat' split <;> simp_all [sharedHadamard_scale, sharedX_scale, sharedZ_scale, sharedT_scale, sharedCNOT_scale]
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all

theorem replayExactNative_scale {n : Nat} (gates : List NativeGate) (k : Cyclo8) (state : SharedDyadicState n) :
    replayExactNative n gates (sharedScale k state) =
      (replayExactNative n gates state).map (sharedScale k) := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    cases h : applyExactNative n gate state with
    | none =>
      have hs : applyExactNative n gate (sharedScale k state) = none := by
        rw [applyExactNative_scale gate k state, h]
        rfl
      simp [replayExactNative, h, hs]
    | some next =>
      have hs : applyExactNative n gate (sharedScale k state) = some (sharedScale k next) := by
        rw [applyExactNative_scale gate k state, h]
        rfl
      simpa [replayExactNative, h, hs] using ih next

end SectorSimulation
