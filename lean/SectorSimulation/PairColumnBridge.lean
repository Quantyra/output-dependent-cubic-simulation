import SectorSimulation.ColumnProgram
import SectorSimulation.PolarPairClearing
namespace SectorSimulation

def matrixColumn {n : Nat} (J : BinaryMatrix n) (j : Fin n) : BinaryVector n := fun i => J i j

def clearPairColumn {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v : Fin n) : BinaryMatrix n :=
  let x := matrixColumn J t
  let a := matrixColumn J u
  let b := matrixColumn J v
  let J₁ := if B x b then safeColumnAdd J t u else J
  if B x a then safeColumnAdd J₁ t v else J₁

theorem clearPairColumn_target {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v : Fin n) (htu : t ≠ u) (htv : t ≠ v) :
    matrixColumn (clearPairColumn B J t u v) t =
      clearPolarPair B (matrixColumn J u) (matrixColumn J v) (matrixColumn J t) := by
  funext i
  cases h1 : B (matrixColumn J t) (matrixColumn J v) <;>
    cases h2 : B (matrixColumn J t) (matrixColumn J u) <;>
    simp [clearPairColumn, matrixColumn, clearPolarPair, selectedBinaryVector,
      safeColumnAdd, columnAdd, binaryShift, htu, htv, Ne.symm htv, h1, h2] <;> cases J i t <;> cases J i u <;> cases J i v <;> rfl

theorem safeColumnAdd_other {n : Nat} (J : BinaryMatrix n) (t u j : Fin n)
    (hjt : j ≠ t) : matrixColumn (safeColumnAdd J t u) j = matrixColumn J j := by
  funext i
  by_cases h : t = u <;> simp [matrixColumn, safeColumnAdd, columnAdd, h, hjt]

theorem clearPairColumn_other {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v j : Fin n) (hjt : j ≠ t) :
    matrixColumn (clearPairColumn B J t u v) j = matrixColumn J j := by
  dsimp only [clearPairColumn]
  split <;> split <;> simp_all [safeColumnAdd_other]
end SectorSimulation
