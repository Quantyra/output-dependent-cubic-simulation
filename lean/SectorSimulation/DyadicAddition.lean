import SectorSimulation.DyadicMultiplication
namespace SectorSimulation

/-- Add using the product of both power-of-two denominators. -/
def dyadicAdd (a b : DyadicCyclo) : DyadicCyclo :=
  ⟨cycloAdd (cycloScale (2 ^ b.exponent) a.numerator) (cycloScale (2 ^ a.exponent) b.numerator),
   a.exponent + b.exponent⟩

def dyadicSubtract (a b : DyadicCyclo) : DyadicCyclo :=
  ⟨cycloSub (cycloScale (2 ^ b.exponent) a.numerator) (cycloScale (2 ^ a.exponent) b.numerator),
   a.exponent + b.exponent⟩

theorem dyadicAdd_congr_left (a b c : DyadicCyclo) (hab : dyadicEquivalent a b) :
    dyadicEquivalent (dyadicAdd a c) (dyadicAdd b c) := by
  let r : Int := 2 ^ c.exponent
  have hh := congrArg (cycloScale (r*r)) hab
  dsimp [r] at hh
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases c with | mk cn ce =>
        cases an; cases bn; cases cn
        simp only [dyadicEquivalent, dyadicAdd, cycloScale, cycloAdd, Cyclo8.mk.injEq,
          Int.pow_add, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at hh ⊢
        constructor <;> omega

theorem dyadicAdd_comm (a b : DyadicCyclo) : dyadicAdd a b = dyadicAdd b a := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases an; cases bn
      simp [dyadicAdd, cycloAdd, cycloScale, Int.add_comm, Nat.add_comm]

theorem dyadicAdd_congr_right (a b c : DyadicCyclo) (hab : dyadicEquivalent a b) :
    dyadicEquivalent (dyadicAdd c a) (dyadicAdd c b) := by
  rw [dyadicAdd_comm c a, dyadicAdd_comm c b]
  exact dyadicAdd_congr_left a b c hab

theorem dyadicAdd_congr (a b c d : DyadicCyclo)
    (hab : dyadicEquivalent a b) (hcd : dyadicEquivalent c d) :
    dyadicEquivalent (dyadicAdd a c) (dyadicAdd b d) := by
  exact dyadicEquivalent_trans _ _ _ (dyadicAdd_congr_left a b c hab)
    (dyadicAdd_congr_right c d b hcd)

def cycloNeg (a : Cyclo8) : Cyclo8 := ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩

def dyadicNeg (a : DyadicCyclo) : DyadicCyclo := ⟨cycloNeg a.numerator, a.exponent⟩

theorem dyadicNeg_congr (a b : DyadicCyclo) (hab : dyadicEquivalent a b) :
    dyadicEquivalent (dyadicNeg a) (dyadicNeg b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases an; cases bn
      simp only [dyadicEquivalent, dyadicNeg, cycloNeg, cycloScale, Cyclo8.mk.injEq,
        Int.mul_neg] at hab ⊢
      obtain ⟨h0,h1,h2,h3⟩ := hab
      simp [h0,h1,h2,h3]

theorem dyadicSubtract_eq_add_neg (a b : DyadicCyclo) :
    dyadicSubtract a b = dyadicAdd a (dyadicNeg b) := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      cases an; cases bn
      simp [dyadicSubtract, dyadicAdd, dyadicNeg, cycloNeg, cycloSub, cycloAdd,
        cycloScale, Int.mul_neg, Int.sub_eq_add_neg]

theorem dyadicSubtract_congr (a b c d : DyadicCyclo)
    (hab : dyadicEquivalent a b) (hcd : dyadicEquivalent c d) :
    dyadicEquivalent (dyadicSubtract a c) (dyadicSubtract b d) := by
  rw [dyadicSubtract_eq_add_neg, dyadicSubtract_eq_add_neg]
  exact dyadicAdd_congr a b (dyadicNeg c) (dyadicNeg d) hab (dyadicNeg_congr c d hcd)

end SectorSimulation
