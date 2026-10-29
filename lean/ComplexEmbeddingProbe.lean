import SectorSimulation.FourierNormalization
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

namespace SectorSimulation

noncomputable def standardOmega : ℂ :=
  ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩

def cycloInterpret (z : ℂ) (a : Cyclo8) : ℂ :=
  (a.c0 : ℂ) + (a.c1 : ℂ)*z + (a.c2 : ℂ)*z^2 + (a.c3 : ℂ)*z^3

theorem standardOmega_fourth : standardOmega^4 = -1 := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [standardOmega, Complex.mul_re, Complex.mul_im, pow_succ, pow_zero] <;> nlinarith


theorem cycloInterpret_mul (z : ℂ) (hz : z^4 = -1) (a b : Cyclo8) :
    cycloInterpret z (cycloMul a b) = cycloInterpret z a * cycloInterpret z b := by
  have hz5 : z^5 = -z := by calc
    z^5 = z^4 * z := by ring
    _ = -z := by rw [hz]; ring
  have hz6 : z^6 = -(z^2) := by calc
    z^6 = z^4 * z^2 := by ring
    _ = -(z^2) := by rw [hz]; ring
  simp only [cycloInterpret, cycloMul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  ring_nf
  rw [hz6, hz5, hz]
  ring

end SectorSimulation
