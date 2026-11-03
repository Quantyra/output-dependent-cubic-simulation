import SectorSimulation.WalshSectorFourier
import SectorSimulation.WalshSectorObservable

/-!
# The Pauli `Z` factor `Z_e` on the computational basis

`Z_e` is the Pauli `Z` on output wire `e`: diagonal in the computational basis, multiplying the
amplitude at label `l` by `(-1)^(l e)`. In the manuscript's observable
`O = F_J D_f1 F_J Z_e F_J D_f1 F_J` it is one of the two non-Fourier factors; the basis change into and
out of the computational basis is carried by the surrounding `F_J` factors, so no Fourier conjugation
belongs in this definition.

Scope, stated because it is easy to overread. This module defines `Z_e` and records that it is an
involution. It does **not** prove the Fourier involution `F_J F_J`, which needs the general character
orthogonality `sum over l of (-1)^(l·v) = 2^n` for `v = 0` and `0` otherwise under a symmetric invertible
pairing — a listed but unproved dependency of `thm:estimator`, and the recorded next target. Nothing here
proves unitarity, `F_J Z_e F_J`, the coset Gauss sum, the offset `eta`, the observable, the matched
vector, any overlap clause or any manuscript correspondence.

No norm or support lemma is recorded: `Z_e` is a diagonal sign, so those are instances of the general
`sectorDiag` facts already in the lane.
-/

namespace SectorSimulation

/-- The Pauli `Z` on wire `e`, acting on a computational-basis amplitude function. -/
def characterZ {n : Nat} (e : Fin n) (f : BinaryVector n → ExactAmplitude) :
    BinaryVector n → ExactAmplitude :=
  fun l => exactSigned (l e) (f l)

/-- Unfolding lemma for `characterZ`. -/
theorem characterZ_apply {n : Nat} (e : Fin n) (f : BinaryVector n → ExactAmplitude)
    (l : BinaryVector n) :
    characterZ e f l = exactSigned (l e) (f l) := rfl

/-- Signing twice by the same sign cancels. -/
theorem exactSigned_involutive (b : Bool) (a : ExactAmplitude) :
    exactSigned b (exactSigned b a) = a := by
  cases b <;> simp [exactSigned, exactNeg_involutive]

/-- `Z_e` is an involution. -/
theorem characterZ_involutive {n : Nat} (e : Fin n)
    (f : BinaryVector n → ExactAmplitude) :
    characterZ e (characterZ e f) = f := by
  funext l
  exact exactSigned_involutive (l e) (f l)

end SectorSimulation
