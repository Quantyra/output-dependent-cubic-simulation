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

end SectorSimulation
