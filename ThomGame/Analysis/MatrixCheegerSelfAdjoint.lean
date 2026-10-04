module

public import ThomGame.Analysis.FiniteCheeger
public import ThomGame.Analysis.MatrixProjectionRankBounds

/-!
# Projection expansion controls all self-adjoint matrices

Diagonalize the actual input matrix, use its eigenbasis to turn
arbitrary index cuts into actual matrix projections, and apply the
finite weighted Cheeger inequality with rho = 1/d.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem hsNorm_diagonal_real_sq (a : Fin d → ℝ) :
    hsNorm (Matrix.diagonal (fun i => (a i : ℂ))) ^ 2 = (∑ i, a i ^ 2) / d := by
  rw [hsNorm_sq]
  simp [Matrix.diagonal_apply, apply_ite, Complex.norm_real]

theorem hsNorm_selfAdjoint_center_spectral {X : CMatrix d} (hX : Matrix.IsHermitian X) (c : ℝ) :
    hsNorm (X - (c : ℂ) • 1) ^ 2 = (∑ i, (hX.eigenvalues i - c) ^ 2) / d := by
  have he : X - (c : ℂ) • 1 = matrixUnitaryConjugation hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hX.eigenvalues i - c : ℝ) : ℂ))) := by
    have hd : Matrix.diagonal (fun i => ((hX.eigenvalues i - c : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) - (c : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hd, map_sub, map_smul, matrixUnitaryConjugation_one]
    exact congrArg (fun A : CMatrix d => A - (c : ℂ) • 1) hX.spectral_theorem
  rw [he, matrixUnitaryConjugation_hsNorm, hsNorm_diagonal_real_sq]

theorem matrixCoordinateEnergy_conjugate_diagonal (V : UnitaryMatrix d) (U : Fin h → UnitaryMatrix d)
    (a : Fin d → ℝ) :
    matrixCoordinateEnergy U (matrixUnitaryConjugation V (Matrix.diagonal (fun i => (a i : ℂ)))) =
      finiteWeightedEnergy (matrixEnergyWeight (fun j => V⁻¹ * U j * V)) a := by
  have he := matrixCoordinateEnergy_conjugate V⁻¹ U
    (matrixUnitaryConjugation V (Matrix.diagonal (fun i => (a i : ℂ))))
  simp only [inv_inv, matrixUnitaryConjugation_inv] at he
  exact he.symm.trans (matrixCoordinateEnergy_diagonal _ _)

theorem matrixBasisProjection_eq_cut_diagonal (V : UnitaryMatrix d) (S : Finset (Fin d)) :
    matrixBasisProjection V S = matrixUnitaryConjugation V
      (Matrix.diagonal (fun i => (finiteCutVector S i : ℂ))) := by
  have he : (fun i => (finiteCutVector S i : ℂ)) = (fun i => if i ∈ S then (1 : ℂ) else 0) := by
    funext i
    by_cases hi : i ∈ S <;> simp [finiteCutVector, hi]
  rw [he]
  rfl

variable [NeZero d] [NeZero h]

theorem matrixCoordinateEnergy_cheeger_selfAdjoint (U : Fin h → UnitaryMatrix d)
    {α : ℝ} (hα : 0 ≤ α)
    (hexpand : ∀ p : CMatrix d, IsStarProjection p → 2 * p.rank ≤ d →
      α * matrixTraceReal d p ≤ matrixCoordinateEnergy U p)
    {X : CMatrix d} (hX : Matrix.IsHermitian X) :
    α ^ 2 * hsNorm (X - ((normalizedTrace X).re : ℂ) • 1) ^ 2 ≤ matrixCoordinateEnergy U X := by
  let V := hX.eigenvectorUnitary
  let W := matrixEigenbasisTuple hX U
  have hrow (i : Fin d) : ∑ j, matrixEnergyWeight W i j = (1 / (d : ℝ)) / 4 := by
    rw [matrixEnergyWeight_row_sum]
    ring
  have hcol (j : Fin d) : ∑ i, matrixEnergyWeight W i j = (1 / (d : ℝ)) / 4 := by
    rw [matrixEnergyWeight_col_sum]
    ring
  have hcut (S : Finset (Fin d)) (hS : 2 * S.card ≤ Fintype.card (Fin d)) :
      α * (1 / (d : ℝ)) * (S.card : ℝ) ≤ finiteWeightedEnergy (matrixEnergyWeight W) (finiteCutVector S) := by
    have hQ := matrixBasisProjection_isStarProjection V S
    have hr : 2 * (matrixBasisProjection V S).rank ≤ d := by
      simpa only [matrixBasisProjection_rank, Fintype.card_fin] using hS
    have hh := hexpand (matrixBasisProjection V S) hQ hr
    rw [matrixTraceReal_projection_rank d hQ, matrixBasisProjection_rank,
      matrixBasisProjection_eq_cut_diagonal, matrixCoordinateEnergy_conjugate_diagonal] at hh
    convert hh using 1 <;> first | rfl | ring
  have hh := finiteWeightedEnergy_cheeger (matrixEnergyWeight W) (matrixEnergyWeight_nonneg W)
    hα (by positivity : (0 : ℝ) ≤ 1 / d) hrow hcol hcut hX.eigenvalues
  rw [hsNorm_selfAdjoint_center_spectral hX, normalizedTrace_eq_eigenvalue_sum hX,
    matrixCoordinateEnergy_spectral hX]
  simpa only [Fintype.card_fin, one_div, div_eq_mul_inv, mul_comm _ ((d : ℝ)⁻¹),
    finiteWeightedEnergy, W, mul_one] using hh

end ThomGame.Analysis
