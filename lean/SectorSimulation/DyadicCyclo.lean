import SectorSimulation.CycloTCommutation
namespace SectorSimulation

/-- An exact eighth-root coefficient divided by 2 to a natural power. -/
structure DyadicCyclo where
  numerator : Cyclo8
  exponent : Nat
  deriving DecidableEq, Repr

def cycloScale (k : Int) (a : Cyclo8) : Cyclo8 :=
  ⟨k*a.c0, k*a.c1, k*a.c2, k*a.c3⟩

def dyadicEquivalent (a b : DyadicCyclo) : Prop :=
  cycloScale (2 ^ b.exponent) a.numerator = cycloScale (2 ^ a.exponent) b.numerator

def dyadicMultiply (a b : DyadicCyclo) : DyadicCyclo :=
  ⟨a.numerator * b.numerator, a.exponent + b.exponent⟩

def dyadicDouble (a : DyadicCyclo) : DyadicCyclo :=
  ⟨cycloScale 2 a.numerator, a.exponent⟩

def dyadicOne : DyadicCyclo := ⟨cycloOne, 0⟩

def dyadicHadamardScale : DyadicCyclo := ⟨cycloSqrtTwo, 1⟩

theorem dyadicEquivalent_refl (a : DyadicCyclo) : dyadicEquivalent a a := by rfl

theorem dyadicEquivalent_symm (a b : DyadicCyclo) :
    dyadicEquivalent a b → dyadicEquivalent b a := by
  intro h
  exact h.symm

/-- Two factors of sqrt(2)/2 and the two-term Hadamard numerator normalize to one. -/
theorem dyadicHadamardScale_normalizes :
    dyadicEquivalent (dyadicDouble (dyadicMultiply dyadicHadamardScale dyadicHadamardScale)) dyadicOne := by
  unfold dyadicEquivalent
  decide

/-- The exact scale squared is one half. -/
theorem dyadicHadamardScale_squared :
    dyadicEquivalent (dyadicMultiply dyadicHadamardScale dyadicHadamardScale) ⟨cycloOne, 1⟩ := by
  unfold dyadicEquivalent
  decide

end SectorSimulation
