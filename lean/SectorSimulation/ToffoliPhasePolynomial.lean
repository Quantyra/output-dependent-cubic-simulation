import SectorSimulation.CubicPhaseInteger
namespace SectorSimulation

/-- Exponent of the eighth root of unity contributed by T and TDG records,
    evaluated on the Boolean wires of the compiler's Toffoli decomposition. -/
def toffoliPhaseExponent (a b t : Bool) : Int :=
  -(if Bool.xor b t then 1 else 0) +
  (if Bool.xor a (Bool.xor b t) then 1 else 0) -
  (if Bool.xor a t then 1 else 0) +
  (if b then 1 else 0) + (if t then 1 else 0) +
  (if a then 1 else 0) - (if Bool.xor a b then 1 else 0)

/-- The target-wire CNOT network in the decomposition restores the target. -/
theorem toffoli_target_network_restores (a b t : Bool) :
    Bool.xor a (Bool.xor b (Bool.xor a (Bool.xor b t))) = t := by
  cases a <;> cases b <;> cases t <;> decide

/-- The control-wire CNOT pair in the decomposition restores the second control. -/
theorem toffoli_control_network_restores (a b : Bool) :
    Bool.xor a (Bool.xor a b) = b := by
  cases a <;> cases b <;> decide

/-- The seven T/TDG phases equal a controlled-controlled-Z sign modulo eight. -/
theorem toffoli_phase_polynomial (a b t : Bool) :
    toffoliPhaseExponent a b t % 8 = (if a && b && t then 4 else 0) := by
  cases a <;> cases b <;> cases t <;> decide

end SectorSimulation
