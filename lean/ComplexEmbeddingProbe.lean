import SectorSimulation.FourierNormalization
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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


theorem cycloInterpret_scale (z : ℂ) (k : Int) (a : Cyclo8) :
    cycloInterpret z (cycloScale k a) = (k : ℂ) * cycloInterpret z a := by
  simp only [cycloInterpret, cycloScale, Int.cast_mul]
  ring

noncomputable def dyadicInterpret (a : DyadicCyclo) : ℂ :=
  cycloInterpret standardOmega a.numerator / (2 : ℂ) ^ a.exponent

theorem dyadicInterpret_congr (a b : DyadicCyclo) (h : dyadicEquivalent a b) :
    dyadicInterpret a = dyadicInterpret b := by
  have h' := congrArg (cycloInterpret standardOmega) h
  simp only [cycloInterpret_scale, Int.cast_pow, Int.cast_ofNat] at h'
  unfold dyadicInterpret
  apply (div_eq_div_iff (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))).2
  simpa only [mul_comm] using h'

noncomputable def exactComplex : ExactAmplitude → ℂ :=
  Quotient.lift dyadicInterpret (fun _ _ h => dyadicInterpret_congr _ _ h)


theorem cycloInterpret_add (z : ℂ) (a b : Cyclo8) :
    cycloInterpret z (cycloAdd a b) = cycloInterpret z a + cycloInterpret z b := by
  simp only [cycloInterpret, cycloAdd, Int.cast_add]
  ring

theorem dyadicInterpret_mul (a b : DyadicCyclo) :
    dyadicInterpret (dyadicMultiply a b) = dyadicInterpret a * dyadicInterpret b := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only [dyadicInterpret, dyadicMultiply, pow_add]
      change cycloInterpret standardOmega (cycloMul an bn) / ((2 : ℂ)^ae * 2^be) = _
      rw [cycloInterpret_mul standardOmega standardOmega_fourth]
      field_simp <;> ring

theorem dyadicInterpret_add (a b : DyadicCyclo) :
    dyadicInterpret (dyadicAdd a b) = dyadicInterpret a + dyadicInterpret b := by
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      simp only [dyadicInterpret, dyadicAdd, cycloInterpret_add, cycloInterpret_scale,
        Int.cast_pow, Int.cast_ofNat, pow_add]
      field_simp <;> ring


theorem exactComplex_add (a b : ExactAmplitude) :
    exactComplex (exactAdd a b) = exactComplex a + exactComplex b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change dyadicInterpret (dyadicAdd a b) = dyadicInterpret a + dyadicInterpret b
      exact dyadicInterpret_add a b

theorem exactComplex_mul (a b : ExactAmplitude) :
    exactComplex (exactMul a b) = exactComplex a * exactComplex b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change dyadicInterpret (dyadicMultiply a b) = dyadicInterpret a * dyadicInterpret b
      exact dyadicInterpret_mul a b

theorem exactComplex_one : exactComplex exactOne = 1 := by
  change dyadicInterpret dyadicOne = 1
  simp [dyadicInterpret, dyadicOne, cycloInterpret, cycloOne]


theorem exactComplex_hadamard :
    exactComplex exactHadamardScale = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
  change dyadicInterpret dyadicHadamardScale = _
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2)^3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2)^3 = (Real.sqrt 2)^2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hs]
  apply Complex.ext <;>
    simp [dyadicInterpret, dyadicHadamardScale,
      cycloInterpret, cycloSqrtTwo, standardOmega, Complex.mul_re, Complex.mul_im,
      pow_succ, pow_zero] <;> nlinarith

theorem exactComplex_iterateHadamardScale (k : Nat) (a : ExactAmplitude) :
    exactComplex (iterateHadamardScale k a) =
      ((((Real.sqrt 2 : ℝ) : ℂ) / 2)^k) * exactComplex a := by
  induction k generalizing a with
  | zero => simp [iterateHadamardScale]
  | succ k ih =>
    simp only [iterateHadamardScale]
    rw [ih, exactComplex_mul, exactComplex_hadamard, pow_succ]
    ring


theorem exactComplex_zero : exactComplex exactZero = 0 := by
  change dyadicInterpret ⟨⟨0,0,0,0⟩,0⟩ = 0
  simp [dyadicInterpret, cycloInterpret]

theorem exactComplex_neg (a : ExactAmplitude) : exactComplex (exactNeg a) = -exactComplex a := by
  induction a using Quotient.ind with
  | _ a =>
    change dyadicInterpret (dyadicNeg a) = -dyadicInterpret a
    cases a with | mk num exp =>
      simp only [dyadicInterpret, dyadicNeg, cycloInterpret, cycloNeg, Int.cast_neg]
      ring

def complexSigned (b : Bool) (a : ℂ) : ℂ := if b then -a else a

theorem exactComplex_signed (b : Bool) (a : ExactAmplitude) :
    exactComplex (exactSigned b a) = complexSigned b (exactComplex a) := by
  cases b <;> simp [exactSigned, complexSigned, exactComplex_neg]

theorem exactComplex_foldr {α : Type} (xs : List α) (f : α → ExactAmplitude) :
    exactComplex (xs.foldr (fun x acc => exactAdd (f x) acc) exactZero) =
      xs.foldr (fun x acc => exactComplex (f x) + acc) 0 := by
  induction xs with
  | nil => exact exactComplex_zero
  | cons x rest ih => simp only [List.foldr_cons, exactComplex_add, ih]

theorem nativePythonFourier_complex_sum {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, exactComplex (sharedAmplitude result x) =
        ((((Real.sqrt 2 : ℝ) : ℂ) / 2)^n) *
        ((binaryBasis n).foldr (fun y acc =>
          complexSigned (matrixPairingParity J x y) (exactComplex (sharedAmplitude state y)) + acc) 0) := by
  obtain ⟨result, hr, hf⟩ := nativePythonFourier_normalized_sum J ops hp state
  refine ⟨result, hr, ?_⟩
  intro x
  rw [hf x, exactComplex_mul, exactComplex_iterateHadamardScale, exactComplex_one, mul_one,
    exactComplex_foldr]
  congr 2
  funext y acc
  rw [exactComplex_signed]


/-- The manuscript normalization agrees with the verified positive square-root factor. -/
theorem realFourierScale_rpow (n : Nat) :
    (Real.sqrt 2 / 2)^n = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have hbase : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    field_simp
    nlinarith [hs]
  rw [hbase, inv_pow]
  have he : -(n : ℝ) / 2 = -((1 / 2 : ℝ) * n) := by ring
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_mul_natCast (by norm_num), ← Real.sqrt_eq_rpow]

end SectorSimulation
