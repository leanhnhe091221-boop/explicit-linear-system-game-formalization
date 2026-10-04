module

public import ThomGame.Analysis.MatrixChannelEnergy
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# The square root of channel energy is a seminorm

The seminorm is defined by the actual trace expression and identified with
the norm of the Kraus commutator differential, divided by square root two.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra BigOperators

variable {d : Nat} [NeZero d]

theorem matrixKrausDifferential_norm_eq {ι : Type*} [Fintype ι]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (a : ι → CMatrix d)
    (hrep : ∀ X, F X = ∑ k, star (a k) * X * a k) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    ‖matrixKrausDifferential a X‖ = Real.sqrt 2 * Real.sqrt (matrixChannelEnergy F X) := by
  have he := (matrixKrausDifferential_norm_sq a X).trans (matrixChannelEnergy_kraus F a hrep hF htrace X)
  have hn : 0 ≤ matrixChannelEnergy F X := by nlinarith [sq_nonneg ‖matrixKrausDifferential a X‖]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hn]
  exact he

theorem matrixUCP_energy_sqrt_add_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X Y : CMatrix d) :
    Real.sqrt (matrixChannelEnergy F.toLinearMap (X + Y)) ≤
      Real.sqrt (matrixChannelEnergy F.toLinearMap X) + Real.sqrt (matrixChannelEnergy F.toLinearMap Y) := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus F
  have hn := matrixKrausDifferential_norm_eq F.toLinearMap a ha hF htrace
  have he := norm_add_le (matrixKrausDifferential a X) (matrixKrausDifferential a Y)
  rw [← map_add, hn, hn, hn, ← mul_add] at he
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp he

theorem matrixUCP_energy_sqrt_smul (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (c : ℂ) (X : CMatrix d) :
    Real.sqrt (matrixChannelEnergy F.toLinearMap (c • X)) =
      ‖c‖ * Real.sqrt (matrixChannelEnergy F.toLinearMap X) := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus F
  have hn := matrixKrausDifferential_norm_eq F.toLinearMap a ha hF htrace
  have he := norm_smul c (matrixKrausDifferential a X)
  rw [← map_smul, hn, hn, mul_left_comm] at he
  exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) he

noncomputable def matrixUCP_energySeminorm (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) : Seminorm ℂ (CMatrix d) :=
  Seminorm.of (fun X => Real.sqrt (matrixChannelEnergy F.toLinearMap X))
    (matrixUCP_energy_sqrt_add_le F hF htrace) (matrixUCP_energy_sqrt_smul F hF htrace)

@[simp] theorem matrixUCP_energySeminorm_apply (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    matrixUCP_energySeminorm F hF htrace X = Real.sqrt (matrixChannelEnergy F.toLinearMap X) := rfl

theorem matrixUCP_energy_le_two_norm_sq (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    matrixChannelEnergy F.toLinearMap X ≤ 2 * hsNorm X ^ 2 := by
  have hc := norm_inner_le_norm (𝕜 := ℂ) (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d (F X))
  rw [finiteMatrixHilbert_inner, finiteMatrixHilbert_norm, finiteMatrixHilbert_norm] at hc
  have hn := matrixUCP_hsNorm_le F hF htrace X
  have hr := Complex.abs_re_le_norm (normalizedTrace (star X * F X))
  have hr' := neg_le_abs (normalizedTrace (star X * F X)).re
  change hsNorm X ^ 2 - (normalizedTrace (star X * F X)).re ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hn (hsNorm_nonneg X)]

theorem matrixUCP_energy_sqrt_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    Real.sqrt (matrixChannelEnergy F.toLinearMap X) ≤ Real.sqrt 2 * hsNorm X := by
  have he := Real.sqrt_le_sqrt (matrixUCP_energy_le_two_norm_sq F hF htrace X)
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (hsNorm_nonneg X)] using he

end ThomGame.Analysis
