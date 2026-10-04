module

public import ThomGame.Analysis.FiniteNoDriftObstruction

/-! Exact transport of unitary words and their normalized distance from one. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n : Nat} (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)

theorem finiteNoDriftFrameUnitary_mul (U V : UnitaryMatrix d) :
    finiteNoDriftFrameUnitary F hF (U * V) =
      finiteNoDriftFrameUnitary F hF U * finiteNoDriftFrameUnitary F hF V := by
  apply Subtype.ext
  change finiteNoDriftFrameValue F (U.val * V.val) 1 =
    finiteNoDriftFrameValue F U.val 1 * finiteNoDriftFrameValue F V.val 1
  rw [finiteNoDriftFrameValue_mul F hF, one_mul]

theorem finiteNoDriftFrameUnitary_inv (U : UnitaryMatrix d) :
    finiteNoDriftFrameUnitary F hF U⁻¹ = (finiteNoDriftFrameUnitary F hF U)⁻¹ := by
  apply Subtype.ext
  change finiteNoDriftFrameValue F U.valᴴ 1 = (finiteNoDriftFrameValue F U.val 1)ᴴ
  rw [finiteNoDriftFrameValue_star F hF, star_one]

theorem finiteNoDriftFrameUnitary_sub_one (U : UnitaryMatrix d) :
    (finiteNoDriftFrameUnitary F hF U).val - 1 = matrixFrameLift F (U.val - 1) := by
  change finiteNoDriftFrameValue F U.val 1 - 1 = _
  simp only [finiteNoDriftFrameValue, one_smul, matrixFrameLift_sub, matrixFrameLift_one]
  abel

theorem finiteNoDriftFrameUnitary_word (H V T : UnitaryMatrix d) :
    finiteNoDriftFrameUnitary F hF (H * (V * T⁻¹) * H⁻¹ * (V * T⁻¹)⁻¹) =
      finiteNoDriftFrameUnitary F hF H *
        (finiteNoDriftFrameUnitary F hF V * (finiteNoDriftFrameUnitary F hF T)⁻¹) *
        (finiteNoDriftFrameUnitary F hF H)⁻¹ *
        (finiteNoDriftFrameUnitary F hF V * (finiteNoDriftFrameUnitary F hF T)⁻¹)⁻¹ := by
  simp only [finiteNoDriftFrameUnitary_mul, finiteNoDriftFrameUnitary_inv]

theorem finiteNoDrift_dimension_factor [NeZero d] {η₀ : ℝ}
    (hη₀ : 0 ≤ η₀) (hη₀small : η₀ ≤ 1 / 2)
    (hdim : |(n : ℝ) / d - 1| ≤ 4 * η₀ ^ 2) : Real.sqrt ((n : ℝ) / d) ≤ 2 := by
  have hr := (le_abs_self ((n : ℝ) / d - 1)).trans hdim
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d))
  nlinarith [Real.sqrt_nonneg ((n : ℝ) / d)]

theorem finiteNoDriftFrameUnitary_recover [NeZero d] [NeZero n]
    (hscale : Real.sqrt ((n : ℝ) / d) ≤ 2) (U : UnitaryMatrix d) {r : ℝ}
    (he : hsNorm ((finiteNoDriftFrameUnitary F hF U).val - 1) ≤ r) :
    hsNorm (U.val - 1) ≤ 2 * r := by
  have hr : 0 ≤ r := (hsNorm_nonneg _).trans he
  rw [finiteNoDriftFrameUnitary_sub_one] at he
  rw [matrixFrameLift_hsNorm_recover (NeZero.pos d) (NeZero.pos n) F hF]
  exact (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hscale hr)

end ThomGame.Analysis
