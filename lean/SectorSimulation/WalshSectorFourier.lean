import SectorSimulation.FourierNormalization
import SectorSimulation.HadamardBasisExpansion
import SectorSimulation.ComplexSemantics
import SectorSimulation.MatrixPairing
import SectorSimulation.ExactHadamard

/-!
# The Fourier factor `F_J` on character-space vectors

The manuscript's observable begins with `F_J`, and the sector lane needed an `F_J` that can act on an
arbitrary character-space function — in particular on the sector amplitude, which is zero off a coset.
What the development already had was operational: `nativePythonFourier_normalized_sum` and
`nativePythonFourier_paper_kernel` say that the *replayed native program* for the modeled Fourier
transform computes the paper kernel on a `SharedDyadicState`. A `SharedDyadicState` carries one shared
exponent and a cyclotomic numerator, so it cannot represent a function that vanishes off a coset.

This module supplies the missing operator, `characterFourier`, at the exact-amplitude level, and ties
it back to the certified replay with `characterFourier_replay`. The tie is the point: without it this
would be an unlinked second transform.

Scope: this is the operator and its action on a basis vector. It is not the observable, it is not
`F_J` applied to a sector state, and the coset Gauss sum that the matched-sector identity needs is
untouched. No symmetry or invertibility of `J` is used anywhere here.
-/

namespace SectorSimulation

/-- The Fourier factor `F_J` on character-space functions, with the paper's `2^(-n/2)` normalization.

The normalization is `iterateHadamardScale n exactOne`, which is `(sqrt 2 / 2)^n` inside the exact
amplitude quotient — a genuine amplitude for every `n`, including odd `n`. -/
noncomputable def characterFourier {n : Nat} (J : BinaryMatrix n)
    (f : BinaryVector n → ExactAmplitude) : BinaryVector n → ExactAmplitude :=
  fun l => exactMul (iterateHadamardScale n exactOne)
    ((binaryBasis n).foldr (fun y acc => exactAdd
      (exactSigned (matrixPairingParity J l y) (f y)) acc) exactZero)

/-- The character-space delta at `c`, recorded through the existing basis-term notation. -/
def characterDelta {n : Nat} (c : BinaryVector n) : BinaryVector n → ExactAmplitude :=
  basisTerm (fun _ => exactOne) c

/-- `characterFourier` is the certified replay program, on states the replay can represent.

This is the bridge that keeps the operator from floating free: on a `SharedDyadicState` it computes
exactly what `nativePythonFourier_normalized_sum` says the replayed native program computes. -/
theorem characterFourier_replay {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      characterFourier J (sharedAmplitude state) = sharedAmplitude result := by
  obtain ⟨result, hr, hf⟩ := nativePythonFourier_normalized_sum J ops hp state
  exact ⟨result, hr, funext (fun x => (hf x).symm)⟩

/-- Collapsing a list sum whose only nonzero term is at `c`. -/
theorem foldr_if_eq_eq {n : Nat} (xs : List (BinaryVector n)) (c : BinaryVector n)
    (v : ExactAmplitude) (hn : xs.Nodup) :
    xs.foldr (fun y acc => exactAdd (if y = c then v else exactZero) acc) exactZero =
      if c ∈ xs then v else exactZero := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases ha : a = c
    · have hnot : c ∉ rest := by
        intro h
        exact hn'.1 (by rw [ha]; exact h)
      have hz : rest.foldr (fun y acc => exactAdd (if y = c then v else exactZero) acc) exactZero
          = exactZero := by
        rw [ih hn'.2, if_neg hnot]
      rw [List.foldr_cons, if_pos ha, hz, exactAdd_zero]
      simp [ha]
    · rw [List.foldr_cons, if_neg ha, exactZero_add, ih hn'.2]
      by_cases hc : c ∈ rest
      · simp [hc]
      · have hca : ¬ (c = a) := fun h => ha h.symm
        simp [hc, hca]

/-- The Fourier factor on a basis term: only the term's own character survives. -/
theorem characterFourier_basisTerm {n : Nat} (J : BinaryMatrix n)
    (g : BinaryVector n → ExactAmplitude) (c l : BinaryVector n) :
    characterFourier J (basisTerm g c) l =
      exactMul (iterateHadamardScale n exactOne)
        (exactSigned (matrixPairingParity J l c) (g c)) := by
  classical
  rw [characterFourier]
  have hpt : ∀ y : BinaryVector n,
      exactSigned (matrixPairingParity J l y) (basisTerm g c y) =
        if y = c then exactSigned (matrixPairingParity J l c) (g c) else exactZero := by
    intro y
    by_cases hy : y = c
    · subst hy
      simp [basisTerm]
    · simp [basisTerm, hy, exactSigned, exactNeg_zero]
  simp only [hpt]
  rw [foldr_if_eq_eq (binaryBasis n) c (exactSigned (matrixPairingParity J l c) (g c))
    (binaryBasis_nodup n), if_pos (binaryBasis_complete c)]

/-- The Fourier factor on a delta returns the paper's normalized character. -/
theorem characterFourier_delta {n : Nat} (J : BinaryMatrix n)
    (c l : BinaryVector n) :
    characterFourier J (characterDelta c) l =
      exactMul (iterateHadamardScale n exactOne)
        (exactSigned (matrixPairingParity J l c) exactOne) :=
  characterFourier_basisTerm J (fun _ => exactOne) c l

/-- The complex form of the delta action: exactly the paper kernel `2^(-n/2) (-1)^(l dot J c)`.

This is a check of the definition's kernel and normalization. It is not a step of the observable
computation: a delta is a basis vector, not a sector amplitude. -/
theorem characterFourier_delta_complex {n : Nat} (J : BinaryMatrix n)
    (c l : BinaryVector n) :
    exactComplex (characterFourier J (characterDelta c) l) =
      ((((2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ)) : ℂ) *
        complexSigned (matrixPairingParity J l c) (1 : ℂ) := by
  rw [characterFourier_delta, exactComplex_mul, exactComplex_iterateHadamardScale,
    exactComplex_one, mul_one, exactComplex_signed, exactComplex_one]
  have hs : ((((Real.sqrt 2 : ℝ) : ℂ) / 2) ^ n) =
      ((((2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ)) : ℂ) := by
    rw [← realFourierScale_rpow]
    push_cast
    rfl
  rw [hs]

end SectorSimulation
