import SectorSimulation.SourceWalshCharacter
namespace SectorSimulation

def recordedCoordinateOrder {n : Nat} (pairs : List (Fin n × Fin n)) : List (Fin n) :=
  pairs.flatMap (fun p => [p.1, p.2]) ++ unpairedIndices (List.finRange n) pairs

theorem pairEndpoints_nodup {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint) :
    (pairs.flatMap (fun p => [p.1, p.2])).Nodup := by
  induction pairs with
  | nil => simp
  | cons p rest ih =>
    have hpr := List.pairwise_cons.mp hp
    have hneq : p.1 ≠ p.2 := hd p (by simp)
    have htail := ih (by intro q hq; exact hd q (by simp [hq])) hpr.2
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false, not_or]
      refine ⟨hneq, ?_⟩
      rintro ⟨q, hq, he | he⟩
      · exact (hpr.1 q hq).1 he.symm
      · exact (hpr.1 q hq).2.2.1 he.symm
    · simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      rintro ⟨q, hq, he | he⟩
      · exact (hpr.1 q hq).2.1 he.symm
      · exact (hpr.1 q hq).2.2.2 he.symm
    · exact htail

theorem recordedCoordinateOrder_perm {n : Nat} (pairs : List (Fin n × Fin n))
    (hd : ∀ p ∈ pairs, p.1 ≠ p.2) (hp : pairs.Pairwise pairDisjoint) :
    (recordedCoordinateOrder pairs).Perm (List.finRange n) := by
  have hn : (recordedCoordinateOrder pairs).Nodup := by
    unfold recordedCoordinateOrder
    apply List.nodup_append.mpr
    refine ⟨pairEndpoints_nodup pairs hd hp, ?_, ?_⟩
    · exact (List.nodup_finRange n).filter _
    · intro i hi j hj he
      subst j
      obtain ⟨p, hpm, hip⟩ := List.mem_flatMap.mp hi
      have h := unpairedIndices_absent (List.finRange n) pairs i hj p hpm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hip
      rcases hip with hi | hi
      · exact h.1 hi
      · exact h.2 hi
  apply List.perm_iff_count.mpr
  intro i
  rw [hn.count, (List.nodup_finRange n).count]
  have hm : i ∈ recordedCoordinateOrder pairs := by
    by_cases h : ∃ p ∈ pairs, i = p.1 ∨ i = p.2
    · obtain ⟨p,hp,hi⟩ := h
      apply List.mem_append.mpr; left
      apply List.mem_flatMap.mpr
      exact ⟨p,hp,by simp [hi]⟩
    · apply List.mem_append.mpr; right
      simp [recordedCoordinateOrder, unpairedIndices]
      intro a b hab
      exact ⟨fun he => h ⟨(a,b),hab,Or.inl he⟩, fun he => h ⟨(a,b),hab,Or.inr he⟩⟩
  simp [hm]



end SectorSimulation