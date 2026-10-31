import SectorSimulation.SourceMixedUnits
namespace SectorSimulation

theorem pairwise_symmetric_members {α : Type} (R : α → α → Prop)
    (hsym : ∀ a b, R a b → R b a) (xs : List α) (h : xs.Pairwise R)
    (a b : α) (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : R a b := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
    have hp := List.pairwise_cons.mp h
    simp only [List.mem_cons] at ha hb
    rcases ha with hax | hat
    · subst a
      rcases hb with hbx | hbt
      · subst b; exact (hne rfl).elim
      · exact hp.1 b hbt
    · rcases hb with hbx | hbt
      · subst b; exact hsym x a (hp.1 a hat)
      · exact ih hp.2 hat hbt

theorem pairDisjoint_symmetric {n : Nat} (p q : Fin n × Fin n)
    (h : pairDisjoint p q) : pairDisjoint q p := by
  exact ⟨Ne.symm h.1, Ne.symm h.2.2.1, Ne.symm h.2.1, Ne.symm h.2.2.2⟩

theorem pairOrthogonal_symmetric {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (hsym : ∀ x y, B x y = B y x)
    (p q : Fin n × Fin n) (h : pairOrthogonal B J p q) : pairOrthogonal B J q p := by
  unfold pairOrthogonal at *
  exact ⟨(hsym _ _).trans h.1, (hsym _ _).trans h.2.2.1,
    (hsym _ _).trans h.2.1, (hsym _ _).trans h.2.2.2⟩
end SectorSimulation
