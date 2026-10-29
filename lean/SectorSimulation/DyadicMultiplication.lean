import SectorSimulation.DyadicEquivalence
namespace SectorSimulation

theorem cycloScale_mul_left (k : Int) (a b : Cyclo8) :
    cycloScale k (a*b) = (cycloScale k a)*b := by
  change cycloScale k (cycloMul a b) = cycloMul (cycloScale k a) b
  cases a; cases b
  simp only [cycloScale, cycloMul, Int.mul_add, Int.mul_sub, Int.mul_assoc]

theorem dyadicMultiply_congr_left (a b c : DyadicCyclo)
    (hab : dyadicEquivalent a b) : dyadicEquivalent (dyadicMultiply a c) (dyadicMultiply b c) := by
  let p : Int := 2 ^ a.exponent
  let q : Int := 2 ^ b.exponent
  let r : Int := 2 ^ c.exponent
  change cycloScale q a.numerator = cycloScale p b.numerator at hab
  change cycloScale (2 ^ (b.exponent + c.exponent)) (a.numerator*c.numerator) =
    cycloScale (2 ^ (a.exponent + c.exponent)) (b.numerator*c.numerator)
  rw [Int.pow_add, Int.pow_add]
  change cycloScale (q*r) (a.numerator*c.numerator) = cycloScale (p*r) (b.numerator*c.numerator)
  rw [← cycloScale_mul, ← cycloScale_mul]
  rw [cycloScale_comm q r, cycloScale_comm p r]
  rw [cycloScale_mul_left, cycloScale_mul_left, hab, cycloScale_mul_left, cycloScale_mul_left]

theorem dyadicMultiply_comm (a b : DyadicCyclo) : dyadicMultiply a b = dyadicMultiply b a := by
  simp [dyadicMultiply, cyclo_mul_comm, Nat.add_comm]

theorem dyadicMultiply_congr_right (a b c : DyadicCyclo)
    (hab : dyadicEquivalent a b) : dyadicEquivalent (dyadicMultiply c a) (dyadicMultiply c b) := by
  rw [dyadicMultiply_comm c a, dyadicMultiply_comm c b]
  exact dyadicMultiply_congr_left a b c hab

theorem dyadicMultiply_congr (a b c d : DyadicCyclo)
    (hab : dyadicEquivalent a b) (hcd : dyadicEquivalent c d) :
    dyadicEquivalent (dyadicMultiply a c) (dyadicMultiply b d) := by
  exact dyadicEquivalent_trans _ _ _ (dyadicMultiply_congr_left a b c hab)
    (dyadicMultiply_congr_right c d b hcd)

end SectorSimulation
