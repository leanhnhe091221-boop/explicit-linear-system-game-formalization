module

public import ThomGame.Analysis.MatrixScalarCornerMass

/-!
# Squared product and scalar-corner errors for high polar completions

The constants are uniform in the ambient dimension and corner ranks.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixUCP_product_fixed_error_sq (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (X Y : CMatrix d) (hX : matrixOpNorm X ≤ 1) (hY : matrixOpNorm Y ≤ 1) :
    hsNorm (F (X * Y) - X * Y) ^ 2 ≤
      4 * (matrixChannelEnergy F.toLinearMap X + matrixChannelEnergy F.toLinearMap Y) := by
  have he := matrixUCP_product_fixed_error F hF htrace X Y hX hY
  have hs := (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).mpr he
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hs
  have hx := Real.sq_sqrt (matrixUCP_energy_nonneg F hF htrace X)
  have hy := Real.sq_sqrt (matrixUCP_energy_nonneg F hF htrace Y)
  nlinarith [sq_nonneg (Real.sqrt (matrixChannelEnergy F.toLinearMap X) -
    Real.sqrt (matrixChannelEnergy F.toLinearMap Y))]

theorem matrixHighPolar_product_scalar_error (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (Q U V : CMatrix d) (rho M : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1)
    (hU : matrixOpNorm U ≤ 1) (hV : matrixOpNorm V ≤ 1) (hmass : hsNorm V ^ 2 ≤ M)
    (heU : matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * M)
    (heV : matrixChannelEnergy F.toLinearMap V ≤ 18 * rho * M)
    (hcorner : hsNorm (F (star U * V) -
      (normalizedTrace (star U * V) / normalizedTrace Q) • Q) ≤ rho ^ 4 * hsNorm (star U * V)) :
    hsNorm (star U * V - (normalizedTrace (star U * V) / normalizedTrace Q) • Q) ^ 2 ≤
      290 * rho * M := by
  have hUs : matrixOpNorm (star U) ≤ 1 := by simpa only [matrixOpNorm_star] using hU
  have hf := matrixUCP_product_fixed_error_sq F hF htrace (star U) V hUs hV
  rw [matrixChannelEnergy_star] at hf
  have hf' : hsNorm (F (star U * V) - star U * V) ^ 2 ≤ 144 * rho * M := by linarith
  have hn : hsNorm (star U * V) ≤ hsNorm V :=
    (hsNorm_mul_le_left _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hUs (hsNorm_nonneg V))
  have hn' : hsNorm (star U * V) ^ 2 ≤ M :=
    ((sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mpr hn).trans hmass
  have hp : (rho ^ 4) ^ 2 ≤ rho := by
    have ht : rho ^ 7 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hrho hsmall 7
    calc
      (rho ^ 4) ^ 2 = rho * rho ^ 7 := by ring
      _ ≤ rho * 1 := mul_le_mul_of_nonneg_left ht hrho
      _ = rho := mul_one rho
  have hc := (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (pow_nonneg hrho _) (hsNorm_nonneg _))).mpr hcorner
  rw [mul_pow] at hc
  have hc' : hsNorm (F (star U * V) -
      (normalizedTrace (star U * V) / normalizedTrace Q) • Q) ^ 2 ≤ rho * M :=
    hc.trans (mul_le_mul hp hn' (sq_nonneg _) hrho)
  have he := hsNorm_add_sq_le_two (star U * V - F (star U * V))
    (F (star U * V) - (normalizedTrace (star U * V) / normalizedTrace Q) • Q)
  rw [sub_add_sub_cancel, hsNorm_sub_comm (star U * V) (F (star U * V))] at he
  linarith

end ThomGame.Analysis
