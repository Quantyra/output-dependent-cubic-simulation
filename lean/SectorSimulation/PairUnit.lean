import SectorSimulation.PolarUnitExt
namespace SectorSimulation

theorem recordedPairPolar_unit_absent {n : Nat} (pairs : List (Fin n × Fin n))
    (i j : Fin n) (h : ∀ p ∈ pairs, i ≠ p.1 ∧ i ≠ p.2) :
    recordedPairPolar pairs (coordinateUnit i) (coordinateUnit j) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht : ∀ q ∈ ps, i ≠ q.1 ∧ i ≠ q.2 := by
      intro q hq; exact h q (by simp [hq])
    simp [recordedPairPolar, coordinateUnit, Ne.symm hp.1, Ne.symm hp.2, ih ht]

theorem recordedPairPolar_head_unit {n : Nat} (p : Fin n × Fin n)
    (ps : List (Fin n × Fin n)) (hne : p.1 ≠ p.2)
    (hdis : ∀ q ∈ ps, pairDisjoint p q) :
    recordedPairPolar (p :: ps) (coordinateUnit p.1) (coordinateUnit p.2) = true := by
  have htail : recordedPairPolar ps (coordinateUnit p.1) (coordinateUnit p.2) = false := by
    apply recordedPairPolar_unit_absent
    intro q hq
    have hd := hdis q hq
    exact ⟨Ne.symm hd.1, Ne.symm hd.2.2.1⟩
  simp [recordedPairPolar, coordinateUnit, hne, Ne.symm hne, htail]

theorem recordedPairPolar_member_unit {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : pairs.Pairwise pairDisjoint)
    (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (p : Fin n × Fin n) (hp : p ∈ pairs) :
    recordedPairPolar pairs (coordinateUnit p.1) (coordinateUnit p.2) = true := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    have hcons := List.pairwise_cons.mp hd
    have htail : ∀ p ∈ qs, p.1 ≠ p.2 := by
      intro p hp; exact hne p (by simp [hp])
    simp only [List.mem_cons] at hp
    rcases hp with he | hm
    · subst q
      exact recordedPairPolar_head_unit p qs (hne p (by simp)) hcons.1
    · have hdis := hcons.1 p hm
      have hrec := ih hcons.2 htail hm
      simp [recordedPairPolar, coordinateUnit, Ne.symm hdis.1, Ne.symm hdis.2.1, hrec]
end SectorSimulation
