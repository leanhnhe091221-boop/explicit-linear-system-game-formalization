module

public import ThomGame.Analysis.MatrixChannelProductEnergy

/-!
# Energy of high eigenvectors and their nearby polar completions

A squared distance bound of 4rho gives a squared energy bound of 18rho,
with the original ambient normalization and no dimension-dependent factor.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra BigOperators

variable {d : Nat}

theorem matrixChannelEnergy_real_eigenvector (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (X : CMatrix d) (lam : ℝ) (heigen : F X = (lam : ℂ) • X) :
    matrixChannelEnergy F X = (1 - lam) * hsNorm X ^ 2 := by
  rw [matrixChannelEnergy, heigen, Matrix.mul_smul, normalizedTrace_smul, normalizedTrace_gram]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

variable [NeZero d]

theorem matrixUCP_energy_perturbation (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X U : CMatrix d) :
    matrixChannelEnergy F.toLinearMap U ≤
      2 * matrixChannelEnergy F.toLinearMap X + 4 * hsNorm (U - X) ^ 2 := by
  have hsum : X + (U - X) = U := by abel
  have he := matrixUCP_energy_sqrt_add_le F hF htrace X (U - X)
  rw [hsum] at he
  have hb := he.trans (add_le_add le_rfl (matrixUCP_energy_sqrt_le F hF htrace (U - X)))
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _)))).mpr hb
  rw [Real.sq_sqrt (matrixUCP_energy_nonneg F hF htrace U)] at hs
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx := Real.sq_sqrt (matrixUCP_energy_nonneg F hF htrace X)
  nlinarith [sq_nonneg (Real.sqrt (matrixChannelEnergy F.toLinearMap X) - Real.sqrt 2 * hsNorm (U - X))]

theorem matrixUCP_high_polar_energy (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (X U : CMatrix d) (lam rho : ℝ) (heigen : F X = (lam : ℂ) • X) (hhigh : 1 - rho ≤ lam)
    (hdist : hsNorm (U - X) ^ 2 ≤ 4 * rho * hsNorm X ^ 2) :
    matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * hsNorm X ^ 2 := by
  have he := matrixUCP_energy_perturbation F hF htrace X U
  rw [matrixChannelEnergy_real_eigenvector F.toLinearMap X lam heigen] at he
  have hl := mul_le_mul_of_nonneg_right (show 1 - lam ≤ rho by linarith) (sq_nonneg (hsNorm X))
  linarith

end ThomGame.Analysis
