# Linear gate computational-basis bridge

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/LinearGateSemantics.lean` SHA-256 `6cc2f62ffdeb769dadea7292e9da8f55da908540cb386386a7f2a9711d011254`.

Lean 4.30.0 locked project build passed (51 jobs). All four declarations have axiom dependencies `[propext, Quot.sound]`. Three modeled distinct-wire CNOTs realize a swap, each distinct-wire CNOT is involutive, and the modeled row-operation-to-CNOT compilation reproduces the action of an arbitrary finite row program on a Boolean basis vector.

The model has not yet proved the reversed elimination sequence realizes the input matrix or matched its emitted records against Python. This is not a quantum-amplitude, physical-circuit, full replay, cost or manuscript-theorem proof.
