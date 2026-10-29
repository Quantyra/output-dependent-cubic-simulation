import SectorSimulation.FourierNormalization
namespace SectorSimulation

def canonicalJoin {k m : Nat} (u v : BinaryVector k) (w : BinaryVector m) : BinaryVector ((k+k)+m) :=
  Fin.addCases (Fin.addCases u v) w

def canonicalLeft {k m : Nat} (x : BinaryVector ((k+k)+m)) : BinaryVector k :=
  fun i => x ((i.castAdd k).castAdd m)

def canonicalRight {k m : Nat} (x : BinaryVector ((k+k)+m)) : BinaryVector k :=
  fun i => x ((Fin.natAdd k i).castAdd m)

def canonicalRadical {k m : Nat} (x : BinaryVector ((k+k)+m)) : BinaryVector m :=
  fun i => x (Fin.natAdd (k+k) i)

theorem canonicalLeft_join {k m : Nat} (u v : BinaryVector k) (w : BinaryVector m) :
    canonicalLeft (canonicalJoin u v w) = u := by
  funext i
  simp [canonicalLeft, canonicalJoin]

theorem canonicalRight_join {k m : Nat} (u v : BinaryVector k) (w : BinaryVector m) :
    canonicalRight (canonicalJoin u v w) = v := by
  funext i
  simp only [canonicalRight, canonicalJoin, Fin.addCases_left, Fin.addCases_right]

theorem canonicalRadical_join {k m : Nat} (u v : BinaryVector k) (w : BinaryVector m) :
    canonicalRadical (canonicalJoin u v w) = w := by
  funext i
  simp [canonicalRadical, canonicalJoin]

theorem canonicalJoin_split {k m : Nat} (x : BinaryVector ((k+k)+m)) :
    canonicalJoin (canonicalLeft x) (canonicalRight x) (canonicalRadical x) = x := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro t
      simp [canonicalJoin, canonicalLeft]
    · intro t
      simp only [canonicalJoin, Fin.addCases_left, Fin.addCases_right, canonicalRight]
  · intro t
    simp [canonicalJoin, canonicalRadical]


theorem canonicalJoin_injective {k m : Nat} (u v u' v' : BinaryVector k)
    (w w' : BinaryVector m) (h : canonicalJoin u v w = canonicalJoin u' v' w') :
    u = u' ∧ v = v' ∧ w = w' := by
  have hl := congrArg canonicalLeft h
  have hr := congrArg canonicalRight h
  have hw := congrArg canonicalRadical h
  simp only [canonicalLeft_join] at hl
  simp only [canonicalRight_join] at hr
  simp only [canonicalRadical_join] at hw
  exact ⟨hl, hr, hw⟩

theorem canonicalSplit_unique {k m : Nat} (x : BinaryVector ((k+k)+m)) :
    ∃ u v : BinaryVector k, ∃ w : BinaryVector m,
      canonicalJoin u v w = x ∧
      ∀ u' v' : BinaryVector k, ∀ w' : BinaryVector m,
        canonicalJoin u' v' w' = x → u' = u ∧ v' = v ∧ w' = w := by
  refine ⟨canonicalLeft x, canonicalRight x, canonicalRadical x, canonicalJoin_split x, ?_⟩
  intro u' v' w' h
  apply canonicalJoin_injective
  rw [h, canonicalJoin_split]

end SectorSimulation
