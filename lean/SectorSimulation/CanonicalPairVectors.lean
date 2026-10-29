import SectorSimulation.CanonicalAssignmentCoverage
namespace SectorSimulation

def vectorPairAssignment {n : Nat} (x y : BinaryVector n) : List (Bool × Bool) :=
  (List.finRange n).map (fun i => (x i, y i))

theorem vectorPairAssignment_length {n : Nat} (x y : BinaryVector n) :
    (vectorPairAssignment x y).length = n := by simp [vectorPairAssignment]

theorem vectorPairAssignment_mem {n : Nat} (x y : BinaryVector n) :
    vectorPairAssignment x y ∈ pairAssignments n := by
  rw [pairAssignments_mem_iff, vectorPairAssignment_length]

theorem vectorPairAssignment_get {n : Nat} (x y : BinaryVector n) (i : Fin n) :
    (vectorPairAssignment x y)[i.val]? = some (x i, y i) := by
  have h : i.val < (vectorPairAssignment x y).length := by simp [vectorPairAssignment, i.isLt]
  rw [List.getElem?_eq_getElem h]
  simp [vectorPairAssignment, List.getElem_finRange]

theorem vectorPairAssignment_injective {n : Nat} (x y x' y' : BinaryVector n)
    (h : vectorPairAssignment x y = vectorPairAssignment x' y') : x = x' ∧ y = y' := by
  have he : ∀ i, (x i, y i) = (x' i, y' i) := by
    intro i
    have hh := congrArg (fun xs : List (Bool × Bool) => xs[i.val]?) h
    simpa only [vectorPairAssignment_get, Option.some.injEq] using hh
  constructor <;> funext i
  · exact congrArg Prod.fst (he i)
  · exact congrArg Prod.snd (he i)

def assignmentPairVectors {n : Nat} (xs : List (Bool × Bool)) (h : xs.length = n) :
    BinaryVector n × BinaryVector n :=
  (fun i => (xs[i.val]'(by simpa [h] using i.isLt)).1,
   fun i => (xs[i.val]'(by simpa [h] using i.isLt)).2)

theorem vectorPairAssignment_roundtrip {n : Nat} (xs : List (Bool × Bool)) (h : xs.length = n) :
    vectorPairAssignment (assignmentPairVectors xs h).1 (assignmentPairVectors xs h).2 = xs := by
  apply List.ext_getElem
  · simpa [vectorPairAssignment_length] using h.symm
  · intro i hi1 hi2
    have hn : i < n := by simpa [vectorPairAssignment_length] using hi1
    have he := vectorPairAssignment_get (assignmentPairVectors xs h).1 (assignmentPairVectors xs h).2 ⟨i, hn⟩
    rw [List.getElem?_eq_getElem hi1] at he
    simpa [assignmentPairVectors] using he

theorem pairAssignment_has_unique_vectors (n : Nat) (xs : List (Bool × Bool))
    (h : xs ∈ pairAssignments n) : ∃ x y : BinaryVector n, vectorPairAssignment x y = xs ∧
      ∀ x' y' : BinaryVector n, vectorPairAssignment x' y' = xs → x' = x ∧ y' = y := by
  have hlen := (pairAssignments_mem_iff n xs).mp h
  refine ⟨(assignmentPairVectors xs hlen).1, (assignmentPairVectors xs hlen).2,
    vectorPairAssignment_roundtrip xs hlen, ?_⟩
  intro x' y' he
  apply vectorPairAssignment_injective
  rw [he, vectorPairAssignment_roundtrip]

end SectorSimulation
