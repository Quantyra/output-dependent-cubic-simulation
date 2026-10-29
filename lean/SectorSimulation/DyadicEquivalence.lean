import SectorSimulation.DyadicCyclo
namespace SectorSimulation

theorem cycloScale_mul (k l : Int) (a : Cyclo8) :
    cycloScale k (cycloScale l a) = cycloScale (k*l) a := by
  cases a
  simp [cycloScale, Int.mul_assoc]

theorem cycloScale_comm (k l : Int) (a : Cyclo8) :
    cycloScale k (cycloScale l a) = cycloScale l (cycloScale k a) := by
  rw [cycloScale_mul, cycloScale_mul, Int.mul_comm]

theorem cycloScale_injective (k : Int) (hk : k ≠ 0) (a b : Cyclo8)
    (h : cycloScale k a = cycloScale k b) : a = b := by
  cases a with
  | mk a0 a1 a2 a3 =>
    cases b with
    | mk b0 b1 b2 b3 =>
      simp only [cycloScale, Cyclo8.mk.injEq] at h
      obtain ⟨h0,h1,h2,h3⟩ := h
      have e0 := Int.eq_of_mul_eq_mul_left hk h0
      have e1 := Int.eq_of_mul_eq_mul_left hk h1
      have e2 := Int.eq_of_mul_eq_mul_left hk h2
      have e3 := Int.eq_of_mul_eq_mul_left hk h3
      simp [e0,e1,e2,e3]

theorem dyadicEquivalent_trans (a b c : DyadicCyclo)
    (hab : dyadicEquivalent a b) (hbc : dyadicEquivalent b c) : dyadicEquivalent a c := by
  let p : Int := 2 ^ a.exponent
  let q : Int := 2 ^ b.exponent
  let r : Int := 2 ^ c.exponent
  have hq : q ≠ 0 := Int.pow_ne_zero (by decide)
  change cycloScale q a.numerator = cycloScale p b.numerator at hab
  change cycloScale r b.numerator = cycloScale q c.numerator at hbc
  change cycloScale r a.numerator = cycloScale p c.numerator
  apply cycloScale_injective q hq
  calc
    cycloScale q (cycloScale r a.numerator) = cycloScale r (cycloScale q a.numerator) := cycloScale_comm q r _
    _ = cycloScale r (cycloScale p b.numerator) := by rw [hab]
    _ = cycloScale p (cycloScale r b.numerator) := cycloScale_comm r p _
    _ = cycloScale p (cycloScale q c.numerator) := by rw [hbc]
    _ = cycloScale q (cycloScale p c.numerator) := cycloScale_comm p q _

end SectorSimulation
