import SectorSimulation.CanonicalCharacterSum

namespace SectorSimulation

theorem finRange_split (a b : Nat) :
    List.finRange (a+b) = (List.finRange a).map (Fin.castAdd b) ++
      (List.finRange b).map (Fin.natAdd a) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_finRange, List.getElem_append, List.length_map, List.length_finRange,
      List.getElem_map]
    split <;> apply Fin.ext <;> simp <;> omega

theorem walshWireParity_append {n : Nat} (xs ys : List (Fin n)) (l x : BinaryVector n) :
    walshWireParity (xs ++ ys) l x = Bool.xor (walshWireParity xs l x) (walshWireParity ys l x) := by
  induction xs with
  | nil => simp [walshWireParity]
  | cons a rest ih => simp [walshWireParity, ih, Bool.xor_assoc]

theorem walshWireParity_map {n p : Nat} (xs : List (Fin n)) (f : Fin n → Fin p)
    (l x : BinaryVector p) :
    walshWireParity (xs.map f) l x = walshWireParity xs (l ∘ f) (x ∘ f) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [walshWireParity, ih, Function.comp_def]

theorem pairLinearEval_map {n : Nat} (xs : List (Fin n)) (l1 l2 x1 x2 : BinaryVector n) :
    pairLinearEval (xs.map (fun i => (l1 i,l2 i))) (xs.map (fun i => (x1 i,x2 i))) =
      Bool.xor (walshWireParity xs l1 x1) (walshWireParity xs l2 x2) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, pairLinearEval, walshWireParity, ih]
    cases l1 a <;> cases l2 a <;> cases x1 a <;> cases x2 a <;>
      cases walshWireParity rest l1 x1 <;> cases walshWireParity rest l2 x2 <;> rfl

theorem radicalLinearEval_map {n : Nat} (xs : List (Fin n)) (l x : BinaryVector n) :
    radicalLinearEval (xs.map l) (xs.map x) = walshWireParity xs l x := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [radicalLinearEval, walshWireParity, ih]


end SectorSimulation
