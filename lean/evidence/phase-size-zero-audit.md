# Phase compiler output size and zero-wire boundary

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source SHA-256: `PhaseCompilerSize.lean` `b8b642dce83d6cbdd34702c946f14e2fa66907db6dc2a854f016eb5564c44151`; `ZeroWirePhaseBoundary.lean` `8e705f08406272a0ccbe1875fe6295d23c9895ea951c22b8f35a4930c078cbcc`.

The locked Lean 4.30.0 build passed (97 jobs). The four size declarations use `[propext, Quot.sound]`; the four zero-wire declarations use `[propext]`. Any successfully compiled phase produces at most 17 native gate records per input monomial. This counts output records only and does not bound compiler runtime.

The modeled native interpreter rejects every gate on zero wires; empty replay preserves the state. Consequently no native record list produces the exact negative amplitude from the specified zero-wire unit state. This does not decide equivalence modulo global phase or measurement observables. Python correspondence, a zero-wire observable treatment, complex embedding, complete circuit behavior, full costs and all labeled manuscript theorems remain open.
