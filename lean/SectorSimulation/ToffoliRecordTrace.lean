import SectorSimulation.ToffoliPhasePolynomial
import SectorSimulation.NativeGateHeader
namespace SectorSimulation

/-- Three wires and a signed exponent of an eighth root of unity. -/
structure ThreeWirePhase where
  a : Bool
  b : Bool
  t : Bool
  exponent : Int
  deriving DecidableEq, Repr

def phaseWire (s : ThreeWirePhase) : Nat → Option Bool
  | 0 => some s.a | 1 => some s.b | 2 => some s.t | _ => none

def setPhaseWire (s : ThreeWirePhase) (wire : Nat) (value : Bool) : Option ThreeWirePhase :=
  match wire with
  | 0 => some { s with a := value }
  | 1 => some { s with b := value }
  | 2 => some { s with t := value }
  | _ => none

def tracePhaseGate (gate : NativeGate) (s : ThreeWirePhase) : Option ThreeWirePhase := do
  match gate with
  | ⟨"CX", [control, target]⟩ =>
    if control = target then none else do
      let c ← phaseWire s control
      let v ← phaseWire s target
      setPhaseWire s target (Bool.xor c v)
  | ⟨"T", [wire]⟩ => do
    let v ← phaseWire s wire
    some { s with exponent := s.exponent + if v then 1 else 0 }
  | ⟨"TDG", [wire]⟩ => do
    let v ← phaseWire s wire
    some { s with exponent := s.exponent - if v then 1 else 0 }
  | _ => none

def tracePhaseRecords : List NativeGate → ThreeWirePhase → Option ThreeWirePhase
  | [], s => some s
  | gate :: rest, s => do
    let next ← tracePhaseGate gate s
    tracePhaseRecords rest next

/-- Literal compiler records for controls 0,1 and target 2, including Hadamards. -/
def nativeToffoli012 : List NativeGate :=
  [⟨"H", [2]⟩, ⟨"CX", [1,2]⟩, ⟨"TDG", [2]⟩, ⟨"CX", [0,2]⟩,
   ⟨"T", [2]⟩, ⟨"CX", [1,2]⟩, ⟨"TDG", [2]⟩, ⟨"CX", [0,2]⟩,
   ⟨"T", [1]⟩, ⟨"T", [2]⟩, ⟨"H", [2]⟩, ⟨"CX", [0,1]⟩,
   ⟨"T", [0]⟩, ⟨"TDG", [1]⟩, ⟨"CX", [0,1]⟩]

/-- Trace the non-H records only.  Reordering the second H needs a separate proof. -/
def toffoliNonHadamardRecords : List NativeGate :=
  nativeToffoli012.filter (fun g => g.tag != "H")

theorem toffoli_literal_phase_trace (a b t : Bool) :
    tracePhaseRecords toffoliNonHadamardRecords ⟨a,b,t,0⟩ =
      some ⟨a,b,t,toffoliPhaseExponent a b t⟩ := by
  cases a <;> cases b <;> cases t <;> decide

theorem toffoli_literal_phase_trace_mod8 (a b t : Bool) :
    ∃ result, tracePhaseRecords toffoliNonHadamardRecords ⟨a,b,t,0⟩ = some result ∧
      result.a = a ∧ result.b = b ∧ result.t = t ∧
      result.exponent % 8 = (if a && b && t then 4 else 0) := by
  refine ⟨⟨a,b,t,toffoliPhaseExponent a b t⟩, toffoli_literal_phase_trace a b t, rfl, rfl, rfl, ?_⟩
  exact toffoli_phase_polynomial a b t

end SectorSimulation
