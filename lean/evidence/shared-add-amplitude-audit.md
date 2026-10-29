# Replay and exact amplitude addition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SharedAdditionAmplitude.lean` SHA-256 `b16d47d926019377e9e5dc2f1c4edf128cf1a4e84740dbdcfa05c443d122fe9d`.

The locked Lean 4.30.0 build passed (80 jobs); all three declarations use `[propext, Classical.choice, Quot.sound]`. Addition of states with equal shared denominator exponents corresponds to addition in the exact amplitude quotient. If replay succeeds for each of two such states, their output denominator exponents agree, and replay of their sum produces the sum of the outputs, with the corresponding exact amplitude sum.

This does not yet decompose arbitrary states into finite basis sums or prove arbitrary-state Toffoli action. Arbitrary wire relabeling, complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
