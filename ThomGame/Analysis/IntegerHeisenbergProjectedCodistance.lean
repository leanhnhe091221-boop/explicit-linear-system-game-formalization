module

public import ThomGame.Analysis.IntegerHeisenbergRefinedCodistance

/-! The local strict estimate with the common fixed component explicitly removed. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem unitaryFixedSpace_residual_fixed (U : H ≃ₗᵢ[ℂ] H) (K : Submodule ℂ H) [CompleteSpace K]
    (hK : K ≤ unitaryFixedSpace U) (w : H) (hw : U w = w) :
    U (Kᗮ.starProjection w) = Kᗮ.starProjection w := by
  rw [Submodule.starProjection_orthogonal_val, map_sub, hw]
  exact congrArg (w - ·) (hK (K.starProjection_apply_mem w))

theorem unitaryFixedSpace_orthogonal_residual (U : H ≃ₗᵢ[ℂ] H) (K : Submodule ℂ H) [CompleteSpace K]
    (hK : K ≤ unitaryFixedSpace U) (w : H) :
    (unitaryFixedSpace U)ᗮ.starProjection (Kᗮ.starProjection w) =
      (unitaryFixedSpace U)ᗮ.starProjection w := by
  rw [Submodule.starProjection_orthogonal_val (K := K), map_sub]
  have hp : (unitaryFixedSpace U)ᗮ.starProjection (K.starProjection w) = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      (unitaryFixedSpace U).starProjection_eq_self_iff.mpr (hK (K.starProjection_apply_mem w)), sub_self]
  rw [hp, sub_zero]

theorem unitaryHeisenberg_projected_four_sum (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z) (hXZ : Commute X Z)
    (a b c d : H) (haX : X a = a) (haZ : Z a = a) (hbY : Y b = b) (hbZ : Z b = b)
    (hcX : X c = c) (hdY : Y d = d) :
    ‖(unitaryCommonFixedSpace X Y)ᗮ.starProjection (a + b + c + d)‖ ^ 2 ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
      2 * (‖(unitaryCommonFixedSpace X Y).starProjection a‖ ^ 2 +
        ‖(unitaryCommonFixedSpace X Y).starProjection b‖ ^ 2 +
        ‖(unitaryCommonFixedSpace X Y).starProjection c‖ ^ 2 +
        ‖(unitaryCommonFixedSpace X Y).starProjection d‖ ^ 2) -
      (1 / 4 : ℝ) * (‖(unitaryFixedSpace Z)ᗮ.starProjection a‖ ^ 2 +
        ‖(unitaryFixedSpace Z)ᗮ.starProjection b‖ ^ 2 +
        ‖(unitaryFixedSpace Z)ᗮ.starProjection c‖ ^ 2 +
        ‖(unitaryFixedSpace Z)ᗮ.starProjection d‖ ^ 2) := by
  let K := unitaryCommonFixedSpace X Y
  let R := Kᗮ.starProjection
  have hKX : K ≤ unitaryFixedSpace X := inf_le_left
  have hKY : K ≤ unitaryFixedSpace Y := inf_le_right
  have hKZ : K ≤ unitaryFixedSpace Z := unitaryHeisenberg_common_le_center X Y Z hrel
  have h := unitaryHeisenberg_refined_four_sum X Y Z hrel hYZ hXZ
    (R a) (R b) (R c) (R d)
    (unitaryFixedSpace_residual_fixed X K hKX a haX)
    (unitaryFixedSpace_residual_fixed Z K hKZ a haZ)
    (unitaryFixedSpace_residual_fixed Y K hKY b hbY)
    (unitaryFixedSpace_residual_fixed Z K hKZ b hbZ)
    (unitaryFixedSpace_residual_fixed X K hKX c hcX)
    (unitaryFixedSpace_residual_fixed Y K hKY d hdY)
    (Kᗮ.starProjection_apply_mem a) (Kᗮ.starProjection_apply_mem c)
  have hsum : R a + R b + R c + R d = R (a + b + c + d) := by simp only [map_add]
  rw [hsum, unitaryFixedSpace_orthogonal_residual Z K hKZ,
    unitaryFixedSpace_orthogonal_residual Z K hKZ] at h
  have hqa : (unitaryFixedSpace Z)ᗮ.starProjection a = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      (unitaryFixedSpace Z).starProjection_eq_self_iff.mpr haZ, sub_self]
  have hqb : (unitaryFixedSpace Z)ᗮ.starProjection b = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      (unitaryFixedSpace Z).starProjection_eq_self_iff.mpr hbZ, sub_self]
  have ha := K.norm_sq_eq_add_norm_sq_starProjection a
  have hb := K.norm_sq_eq_add_norm_sq_starProjection b
  have hc := K.norm_sq_eq_add_norm_sq_starProjection c
  have hd := K.norm_sq_eq_add_norm_sq_starProjection d
  change ‖R (a + b + c + d)‖ ^ 2 ≤
    2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
    2 * (‖K.starProjection a‖ ^ 2 + ‖K.starProjection b‖ ^ 2 +
      ‖K.starProjection c‖ ^ 2 + ‖K.starProjection d‖ ^ 2) - _
  rw [hqa, hqb, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, zero_add]
  linarith

end ThomGame.Analysis
