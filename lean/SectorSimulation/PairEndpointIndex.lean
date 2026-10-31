import SectorSimulation.RecordedCoordinateMap
namespace SectorSimulation

theorem pairEndpoints_length {n : Nat} (pairs : List (Fin n × Fin n)) :
    (pairs.flatMap (fun p => [p.1,p.2])).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p rest ih => simp [ih, Nat.mul_succ]

theorem pairEndpoints_get_first {n : Nat} (pairs : List (Fin n × Fin n))
    (i : Nat) (hi : i < pairs.length) :
    (pairs.flatMap (fun p => [p.1,p.2]))[2*i]'(by rw [pairEndpoints_length]; omega) = pairs[i].1 := by
  induction pairs generalizing i with
  | nil => simp at hi
  | cons p rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, Nat.mul_succ, Nat.add_succ, List.getElem_cons_succ] using ih i hi'

theorem pairEndpoints_get_second {n : Nat} (pairs : List (Fin n × Fin n))
    (i : Nat) (hi : i < pairs.length) :
    (pairs.flatMap (fun p => [p.1,p.2]))[2*i+1]'(by rw [pairEndpoints_length]; omega) = pairs[i].2 := by
  induction pairs generalizing i with
  | nil => simp at hi
  | cons p rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, Nat.mul_succ, Nat.add_succ, List.getElem_cons_succ] using ih i hi'




end SectorSimulation