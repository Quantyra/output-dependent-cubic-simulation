import SectorSimulation.RecordedCoordinateOrder
namespace SectorSimulation

def recordedCoordinateAt {n : Nat} (pairs : List (Fin n × Fin n))
    (hlen : (recordedCoordinateOrder pairs).length = n) (i : Fin n) : Fin n :=
  (recordedCoordinateOrder pairs).get ⟨i.val, by simpa [hlen] using i.isLt⟩

theorem recordedCoordinateAt_bijective {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint) :
    let hlen : (recordedCoordinateOrder pairs).length = n := by
      simpa using (recordedCoordinateOrder_perm pairs hd hp).length_eq
    Function.Injective (recordedCoordinateAt pairs hlen) ∧
      ∀ x, ∃ i, recordedCoordinateAt pairs hlen i = x := by
  dsimp only
  let hperm := recordedCoordinateOrder_perm pairs hd hp
  have hlen : (recordedCoordinateOrder pairs).length = n := by simpa using hperm.length_eq
  have hn : (recordedCoordinateOrder pairs).Nodup := hperm.nodup_iff.mpr (List.nodup_finRange n)
  constructor
  · intro i j he
    apply Fin.ext
    exact (List.getElem_inj hn).mp he
  · intro x
    have hx : x ∈ recordedCoordinateOrder pairs := hperm.mem_iff.mpr (List.mem_finRange x)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
    refine ⟨⟨j.val, by simpa [hlen] using j.isLt⟩, ?_⟩
    exact hj


end SectorSimulation