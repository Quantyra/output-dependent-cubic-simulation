# Mapped native Toffoli correctness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MappedNativeToffoli.lean` SHA-256 `dadb2517f92f9bffd49de9e0a49ca4c4de1dc0b40747185ec417776da0d5c8a1`.

The locked Lean 4.30.0 build passed (87 jobs). The gate and program correspondence declarations use `[propext]`, Toffoli validity uses `[propext, Quot.sound]`, and Toffoli correctness uses `[propext, Classical.choice, Quot.sound]`. For any injective selection of three wires, valid typed programs map to native records whose replay equals typed execution. Therefore the mapped Toffoli record sequence successfully replays on any represented state and has the modeled ideal Toffoli amplitude at every output vector.

Correspondence with Python compiler records, complex embedding, full circuit behavior, costs and all labeled manuscript theorems remain open.
