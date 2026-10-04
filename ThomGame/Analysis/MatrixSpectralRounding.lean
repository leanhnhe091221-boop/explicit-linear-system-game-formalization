module

public import ThomGame.Analysis.MatrixProjectionDistance
public import ThomGame.Analysis.MatrixFamilySpectralCoarea

/-!
# Rounding by spectral cuts

Every cut at a threshold between one third and two thirds is within
nine times the squared distance to any comparison projection. The
comparison projection need not commute with the self-adjoint matrix.
-/

@[expose] public section
namespace ThomGame.Analysis

open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem spectralStep_projection_distance_le (x b s : ℝ) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hs : s ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    spectralStep s x ^ 2 * (1 - b) + (1 - spectralStep s x) ^ 2 * b ≤
      9 * (x ^ 2 * (1 - b) + (1 - x) ^ 2 * b) := by
  by_cases hx : s ≤ x
  · have hx₀ : 1 / 3 ≤ x := hs.1.trans hx
    have hx₂ : 0 ≤ 9 * x ^ 2 - 1 := by nlinarith
    have h₁ := mul_nonneg hx₂ (sub_nonneg.mpr hb₁)
    have h₂ := mul_nonneg (sq_nonneg (1 - x)) hb₀
    simp only [spectralStep, ite_eq_left hx, one_pow, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero, one_mul]
    nlinarith
  · have hx₁ : x ≤ 2 / 3 := (le_of_not_ge hx).trans hs.2
    have hx₂ : 0 ≤ 9 * (1 - x) ^ 2 - 1 := by nlinarith
    have h₁ := mul_nonneg hx₂ hb₀
    have h₂ := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hb₁)
    simp only [spectralStep, ite_eq_right hx, zero_pow (by decide : 2 ≠ 0),
      zero_mul, zero_add, sub_zero, one_pow, one_mul]
    nlinarith

variable {d : Nat} {X P : CMatrix d}

theorem hsNorm_diagonal_spectralStep_sub_projection_le (e : Fin d → ℝ)
    (hP : IsStarProjection P) (s : ℝ) (hs : s ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    hsNorm (Matrix.diagonal (fun i => (spectralStep s (e i) : ℂ)) - P) ^ 2 ≤
      9 * hsNorm (Matrix.diagonal (fun i => (e i : ℂ)) - P) ^ 2 := by
  rw [hsNorm_diagonal_sub_projection_sq _ hP, hsNorm_diagonal_sub_projection_sq _ hP,
    ← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  exact Finset.sum_le_sum fun i _ => spectralStep_projection_distance_le (e i) (P i i).re s
    (matrixProjection_diagonal_bounds hP i).1 (matrixProjection_diagonal_bounds hP i).2 hs

theorem matrixSpectralCut_distance_le (hX : Matrix.IsHermitian X) (hP : IsStarProjection P)
    (s : ℝ) (hs : s ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    hsNorm (matrixSpectralCut X s - P) ^ 2 ≤ 9 * hsNorm (X - P) ^ 2 := by
  let V : UnitaryMatrix d := hX.eigenvectorUnitary
  let Q : CMatrix d := matrixUnitaryConjugation V⁻¹ P
  have hQ : IsStarProjection Q := hP.map (Unitary.conjStarAlgAut ℂ (CMatrix d) V⁻¹)
  have heX : matrixUnitaryConjugation V⁻¹ X = Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) :=
    hX.conjStarAlgAut_star_eigenvectorUnitary
  have heS : matrixUnitaryConjugation V⁻¹ (matrixSpectralCut X s) =
      Matrix.diagonal (fun i => (spectralStep s (hX.eigenvalues i) : ℂ)) := by
    rw [matrixSpectralCut_eq_conjugate hX]
    exact matrixUnitaryConjugation_inv V _
  have hleft : hsNorm (matrixSpectralCut X s - P) =
      hsNorm (Matrix.diagonal (fun i => (spectralStep s (hX.eigenvalues i) : ℂ)) - Q) := by
    rw [← matrixUnitaryConjugation_hsNorm V⁻¹ (matrixSpectralCut X s - P), map_sub, heS]
  have hright : hsNorm (X - P) = hsNorm (Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) - Q) := by
    rw [← matrixUnitaryConjugation_hsNorm V⁻¹ (X - P), map_sub, heX]
  rw [hleft, hright]
  exact hsNorm_diagonal_spectralStep_sub_projection_le _ hQ s hs

theorem matrixSpectralInterval_distance_le (hX : Matrix.IsHermitian X) (hX₁ : X ≤ 1)
    (hP : IsStarProjection P) (s : ℝ) (hs : s ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    hsNorm (matrixSpectralInterval X s 1 - P) ^ 2 ≤ 9 * hsNorm (X - P) ^ 2 := by
  rw [matrixSpectralInterval_one_eq_cut hX hX₁]
  exact matrixSpectralCut_distance_le hX hP s hs

end ThomGame.Analysis
