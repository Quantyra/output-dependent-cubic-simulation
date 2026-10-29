import SectorSimulation.FourierNormalization
namespace SectorSimulation

def integerWalshSign (b : Bool) : Int := if b then -1 else 1

def hyperbolicPhase (a b u v : Bool) : Bool :=
  Bool.xor (u && v) (Bool.xor (a && u) (b && v))

def hyperbolicWalshSum : List (Bool × Bool) → Bool → Int
  | [], c => integerWalshSign c
  | (a,b)::rest, c =>
    hyperbolicWalshSum rest (Bool.xor c (hyperbolicPhase a b false false)) +
    hyperbolicWalshSum rest (Bool.xor c (hyperbolicPhase a b false true)) +
    hyperbolicWalshSum rest (Bool.xor c (hyperbolicPhase a b true false)) +
    hyperbolicWalshSum rest (Bool.xor c (hyperbolicPhase a b true true))

def hyperbolicSignature : List (Bool × Bool) → Bool
  | [] => false
  | (a,b)::rest => Bool.xor (a && b) (hyperbolicSignature rest)

theorem hyperbolicWalshSum_closed (params : List (Bool × Bool)) (c : Bool) :
    hyperbolicWalshSum params c = (2 : Int)^params.length *
      integerWalshSign (Bool.xor c (hyperbolicSignature params)) := by
  induction params generalizing c with
  | nil => cases c <;> rfl
  | cons p rest ih =>
    rcases p with ⟨a,b⟩
    cases hsig : hyperbolicSignature rest <;> cases a <;> cases b <;> cases c <;>
      simp [hyperbolicWalshSum, hyperbolicSignature, hyperbolicPhase, ih,
        integerWalshSign, Int.pow_succ, hsig] <;> omega


def canonicalWalshSum (pairs : List (Bool × Bool)) : List Bool → Bool → Int
  | [], c => hyperbolicWalshSum pairs c
  | b::rest, c => canonicalWalshSum pairs rest c + canonicalWalshSum pairs rest (Bool.xor c b)

theorem canonicalWalshSum_closed (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool) :
    canonicalWalshSum pairs radicals c =
      if radicals.any id then 0 else (2 : Int)^(radicals.length + pairs.length) *
        integerWalshSign (Bool.xor c (hyperbolicSignature pairs)) := by
  induction radicals generalizing c with
  | nil => simpa [canonicalWalshSum] using hyperbolicWalshSum_closed pairs c
  | cons b rest ih =>
    cases hsig : hyperbolicSignature pairs <;> cases hr : rest.any id <;> cases b <;> cases c <;>
      simp [canonicalWalshSum, ih, hsig, hr, integerWalshSign, Int.pow_succ,
        Nat.succ_add] <;> omega

end SectorSimulation
