import SectorSimulation.ExplicitCanonicalWalsh
namespace SectorSimulation

theorem radicalAssignments_complete (xs : List Bool) : xs ∈ radicalAssignments xs.length := by
  induction xs with
  | nil => simp [radicalAssignments]
  | cons x rest ih =>
    cases x <;> simp [radicalAssignments, ih]

theorem pairAssignments_complete (xs : List (Bool × Bool)) : xs ∈ pairAssignments xs.length := by
  induction xs with
  | nil => simp [pairAssignments]
  | cons x rest ih =>
    rcases x with ⟨a,b⟩
    cases a <;> cases b <;> simp [pairAssignments, ih]

theorem radicalAssignments_length (n : Nat) : (radicalAssignments n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [radicalAssignments, ih, Nat.pow_succ]; omega

theorem pairAssignments_length (n : Nat) : (pairAssignments n).length = 4^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairAssignments, ih, Nat.pow_succ]; omega


theorem radicalAssignments_mem_iff (n : Nat) (xs : List Bool) :
    xs ∈ radicalAssignments n ↔ xs.length = n := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [radicalAssignments]
  | succ n ih =>
    cases xs with
    | nil => simp [radicalAssignments]
    | cons a rest => cases a <;> simp [radicalAssignments, ih]

theorem pairAssignments_mem_iff (n : Nat) (xs : List (Bool × Bool)) :
    xs ∈ pairAssignments n ↔ xs.length = n := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [pairAssignments]
  | succ n ih =>
    cases xs with
    | nil => simp [pairAssignments]
    | cons a rest =>
      rcases a with ⟨a,b⟩
      cases a <;> cases b <;> simp [pairAssignments, ih]


theorem nodup_cons_map {α : Type} (a : α) (xs : List (List α)) :
    (xs.map (fun x => a :: x)).Nodup ↔ xs.Nodup := by
  change List.Pairwise (fun x y => x ≠ y) (xs.map (fun x => a :: x)) ↔ List.Pairwise (fun x y => x ≠ y) xs
  rw [List.pairwise_map]
  simp

theorem radicalAssignments_nodup (n : Nat) : (radicalAssignments n).Nodup := by
  induction n with
  | zero => simp [radicalAssignments]
  | succ n ih =>
    simp [radicalAssignments, List.nodup_append, nodup_cons_map, ih]

theorem pairAssignments_nodup (n : Nat) : (pairAssignments n).Nodup := by
  induction n with
  | zero => simp [pairAssignments]
  | succ n ih =>
    simp [pairAssignments, List.nodup_append, nodup_cons_map, ih]
    constructor
    · intro a ha b hb
      rcases hb with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ <;> simp
    · intro a ha b hb
      rcases hb with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ <;> simp


def vectorAssignment {n : Nat} (x : BinaryVector n) : List Bool := (List.finRange n).map x

theorem vectorAssignment_length {n : Nat} (x : BinaryVector n) : (vectorAssignment x).length = n := by
  simp [vectorAssignment]

theorem vectorAssignment_mem {n : Nat} (x : BinaryVector n) : vectorAssignment x ∈ radicalAssignments n := by
  rw [radicalAssignments_mem_iff, vectorAssignment_length]

theorem vectorAssignment_get {n : Nat} (x : BinaryVector n) (i : Fin n) :
    (vectorAssignment x)[i.val]? = some (x i) := by
  have h : i.val < (vectorAssignment x).length := by simp [vectorAssignment, i.isLt]
  rw [List.getElem?_eq_getElem h]
  simp [vectorAssignment, List.getElem_finRange]

theorem vectorAssignment_injective (n : Nat) : Function.Injective (@vectorAssignment n) := by
  intro x y h
  funext i
  have he := congrArg (fun xs : List Bool => xs[i.val]?) h
  simpa only [vectorAssignment_get, Option.some.injEq] using he


def assignmentVector {n : Nat} (xs : List Bool) (h : xs.length = n) : BinaryVector n :=
  fun i => xs[i.val]'(by simpa [h] using i.isLt)

theorem vectorAssignment_of_assignmentVector {n : Nat} (xs : List Bool) (h : xs.length = n) :
    vectorAssignment (assignmentVector xs h) = xs := by
  apply List.ext_getElem
  · simpa [vectorAssignment_length] using h.symm
  · intro i hi1 hi2
    have hn : i < n := by simpa [vectorAssignment_length] using hi1
    have he := vectorAssignment_get (assignmentVector xs h) ⟨i, hn⟩
    rw [List.getElem?_eq_getElem hi1] at he
    simpa [assignmentVector] using he

theorem radicalAssignment_has_unique_vector (n : Nat) (xs : List Bool)
    (h : xs ∈ radicalAssignments n) : ∃ x : BinaryVector n, vectorAssignment x = xs ∧
      ∀ y : BinaryVector n, vectorAssignment y = xs → y = x := by
  have hlen := (radicalAssignments_mem_iff n xs).mp h
  refine ⟨assignmentVector xs hlen, vectorAssignment_of_assignmentVector xs hlen, ?_⟩
  intro y hy
  apply vectorAssignment_injective n
  rw [hy, vectorAssignment_of_assignmentVector]

end SectorSimulation
