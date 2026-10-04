module

public import ThomGame.Analysis.MatrixHermitianEnergyParts

/-!
# Quantum Cheeger inequality for an actual matrix unitary tuple

Half-rank projection expansion alpha gives scalar gap alpha squared
for every complex matrix, using the original normalized trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] [NeZero h]

theorem matrixCoordinateEnergy_cheeger (U : Fin h → UnitaryMatrix d)
    {α : ℝ} (hα : 0 ≤ α)
    (hexpand : ∀ p : CMatrix d, IsStarProjection p → 2 * p.rank ≤ d →
      α * matrixTraceReal d p ≤ matrixCoordinateEnergy U p)
    (X : CMatrix d) :
    α ^ 2 * hsNorm (X - normalizedTrace X • 1) ^ 2 ≤ matrixCoordinateEnergy U X := by
  let A : CMatrix d := realPart X
  let B : CMatrix d := imaginaryPart X
  have hA : IsSelfAdjoint A := (realPart X).property
  have hB : IsSelfAdjoint B := (imaginaryPart X).property
  have hEA := matrixCoordinateEnergy_cheeger_selfAdjoint U hα hexpand hA.isHermitian
  have hEB := matrixCoordinateEnergy_cheeger_selfAdjoint U hα hexpand hB.isHermitian
  rw [normalizedTrace_selfAdjoint_real hA] at hEA
  rw [normalizedTrace_selfAdjoint_real hB] at hEB
  have he : A + Complex.I • B = X := realPart_add_I_smul_imaginaryPart X
  rw [← he, hsNorm_center_selfAdjoint_add_I_smul_sq hA hB,
    matrixCoordinateEnergy_selfAdjoint_add_I_smul U hA hB, mul_add]
  exact add_le_add hEA hEB

end ThomGame.Analysis
