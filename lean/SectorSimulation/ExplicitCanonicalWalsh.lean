import SectorSimulation.CanonicalWalsh
namespace SectorSimulation

def pairAssignments : Nat → List (List (Bool × Bool))
  | 0 => [[]]
  | n+1 =>
    let rest := pairAssignments n
    rest.map (fun xs => (false,false)::xs) ++ rest.map (fun xs => (false,true)::xs) ++
    rest.map (fun xs => (true,false)::xs) ++ rest.map (fun xs => (true,true)::xs)

def pairPhaseEval : List (Bool × Bool) → List (Bool × Bool) → Bool → Bool
  | [], _, c => c
  | (a,b)::ps, (u,v)::xs, c => pairPhaseEval ps xs (Bool.xor c (hyperbolicPhase a b u v))
  | _::_, [], c => c

def explicitPairSum (pairs : List (Bool × Bool)) (c : Bool) : Int :=
  ((pairAssignments pairs.length).map (fun xs => integerWalshSign (pairPhaseEval pairs xs c))).sum

theorem explicitPairSum_eq (pairs : List (Bool × Bool)) (c : Bool) :
    explicitPairSum pairs c = hyperbolicWalshSum pairs c := by
  induction pairs generalizing c with
  | nil => simp [explicitPairSum, pairAssignments, pairPhaseEval, hyperbolicWalshSum]
  | cons p rest ih =>
    rcases p with ⟨a,b⟩
    simp only [explicitPairSum, List.length_cons, pairAssignments, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, pairPhaseEval, hyperbolicWalshSum]
    change explicitPairSum rest (Bool.xor c (hyperbolicPhase a b false false)) +
      explicitPairSum rest (Bool.xor c (hyperbolicPhase a b false true)) +
      explicitPairSum rest (Bool.xor c (hyperbolicPhase a b true false)) +
      explicitPairSum rest (Bool.xor c (hyperbolicPhase a b true true)) = _
    simp [ih, Int.add_assoc]


def radicalAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (radicalAssignments n).map (false :: ·) ++
      (radicalAssignments n).map (true :: ·)

def radicalPhaseEval : List Bool → List Bool → Bool → Bool
  | [], _, c => c
  | b::bs, x::xs, c => radicalPhaseEval bs xs (Bool.xor c (b && x))
  | _::_, [], c => c

def explicitCanonicalSum (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool) : Int :=
  ((radicalAssignments radicals.length).map (fun xs =>
    explicitPairSum pairs (radicalPhaseEval radicals xs c))).sum

theorem explicitCanonicalSum_eq (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool) :
    explicitCanonicalSum pairs radicals c = canonicalWalshSum pairs radicals c := by
  induction radicals generalizing c with
  | nil => simp [explicitCanonicalSum, radicalAssignments, radicalPhaseEval, canonicalWalshSum, explicitPairSum_eq]
  | cons b rest ih =>
    simp only [explicitCanonicalSum, radicalAssignments, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, radicalPhaseEval, canonicalWalshSum]
    change explicitCanonicalSum pairs rest (Bool.xor c (b && false)) +
      explicitCanonicalSum pairs rest (Bool.xor c (b && true)) = _
    simp [ih]

theorem explicitCanonicalSum_closed (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool) :
    explicitCanonicalSum pairs radicals c =
      if radicals.any id then 0 else (2 : Int)^(radicals.length + pairs.length) *
        integerWalshSign (Bool.xor c (hyperbolicSignature pairs)) := by
  rw [explicitCanonicalSum_eq, canonicalWalshSum_closed]

end SectorSimulation
