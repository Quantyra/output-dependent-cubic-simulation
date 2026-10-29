import SectorSimulation.ExactNativeReplay
namespace SectorSimulation

/-- Numerator addition for states sharing a denominator. -/
def sharedAddSame {n : Nat} (a b : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => cycloAdd (a.numerator x) (b.numerator x), a.exponent⟩

theorem sharedHadamard_add {n : Nat} (wire : Fin n) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    sharedHadamard wire (sharedAddSame a b) =
      sharedAddSame (sharedHadamard wire a) (sharedHadamard wire b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      simp only [sharedHadamard, sharedAddSame]
      congr 1
      funext x
      simp only [cycloHadamardNumerator]
      cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        cases ha : an x <;> cases hb : bn x <;>
        cases haf : an (flipWire wire x) <;> cases hbf : bn (flipWire wire x) <;>
        simp only [cycloAdd, cycloSub, cycloMul, cycloSqrtTwo, Cyclo8.mk.injEq] <;> omega

theorem sharedCNOT_add {n : Nat} (control target : Fin n) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    sharedCNOT control target (sharedAddSame a b) =
      sharedAddSame (sharedCNOT control target a) (sharedCNOT control target b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      rfl

theorem sharedX_add {n : Nat} (wire : Fin n) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    sharedX wire (sharedAddSame a b) = sharedAddSame (sharedX wire a) (sharedX wire b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      rfl

theorem sharedZ_add {n : Nat} (wire : Fin n) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    sharedZ wire (sharedAddSame a b) = sharedAddSame (sharedZ wire a) (sharedZ wire b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      simp only [sharedZ, sharedAddSame]
      congr 1
      funext x
      cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        cases ha : an x <;> cases hb : bn x <;>
        simp only [cycloNeg, cycloAdd, Cyclo8.mk.injEq] <;> omega

theorem sharedT_add {n : Nat} (wire : Fin n) (inverse : Bool) (a b : SharedDyadicState n)
    (h : a.exponent = b.exponent) :
    sharedT wire inverse (sharedAddSame a b) = sharedAddSame (sharedT wire inverse a) (sharedT wire inverse b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only at h
      subst be
      simp only [sharedT, sharedAddSame]
      congr 1
      funext x
      cases hx : x wire <;> simp only [Bool.false_eq_true, if_false, if_true]
      exact cyclo_mul_add (if inverse then cycloOmegaInv else cycloOmega) (an x) (bn x)

end SectorSimulation
