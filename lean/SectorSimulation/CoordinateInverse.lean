import SectorSimulation.SourceReindexComplete
namespace SectorSimulation

noncomputable def coordinateInverse {n : Nat} (f : Fin n → Fin n)
    (hsurj : ∀ x, ∃ i, f i = x) (x : Fin n) : Fin n := Classical.choose (hsurj x)

theorem coordinateInverse_right {n : Nat} (f : Fin n → Fin n)
    (hsurj : ∀ x, ∃ i, f i = x) (x : Fin n) : f (coordinateInverse f hsurj x) = x :=
  Classical.choose_spec (hsurj x)

theorem coordinateInverse_left {n : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f) (hsurj : ∀ x, ∃ i, f i = x) (x : Fin n) :
    coordinateInverse f hsurj (f x) = x := hinj (coordinateInverse_right f hsurj (f x))

theorem coordinateInverse_bijective {n : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f) (hsurj : ∀ x, ∃ i, f i = x) :
    Function.Injective (coordinateInverse f hsurj) ∧ ∀ x, ∃ i, coordinateInverse f hsurj i = x := by
  constructor
  · intro a b h; have hh := congrArg f h; simpa only [coordinateInverse_right] using hh
  · intro x; exact ⟨f x, coordinateInverse_left f hinj hsurj x⟩

theorem coordinateReindex_inverse_at {n : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f) (hsurj : ∀ x, ∃ i, f i = x)
    (y : BinaryVector n) (i : Fin n) :
    coordinateReindex (coordinateInverse f hsurj) y (f i) = y i := by
  simp [coordinateReindex, coordinateInverse_left f hinj hsurj]



end SectorSimulation