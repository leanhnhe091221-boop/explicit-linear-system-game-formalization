module

public import ThomGame.Analysis.IntegerHeisenbergTriangle

/-! A strict local improvement on the orthogonal complement of common fixed vectors. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem unitaryHeisenberg_common_le_center (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) : unitaryCommonFixedSpace X Y ≤ unitaryFixedSpace Z := by
  intro w hw
  have hwX : X w = w := hw.1
  have hwY : Y w = w := hw.2
  have h := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hrel
  change Y (X w) = X (Z (Y w)) at h
  rw [hwX, hwY] at h
  exact X.injective (h.symm.trans hwX.symm)

theorem unitaryHeisenberg_common_project_center (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (w : H) :
    (unitaryCommonFixedSpace X Y).starProjection ((unitaryFixedSpace Z).starProjection w) =
      (unitaryCommonFixedSpace X Y).starProjection w :=
  congrArg (fun T : H →L[ℂ] H => T w)
    (Submodule.starProjection_comp_starProjection_of_le (unitaryHeisenberg_common_le_center X Y Z hrel))

theorem unitaryHeisenberg_mixed_residual_orthogonal (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (a b : H) (haX : X a = a) (haZ : Z a = a) (hbY : Y b = b)
    (haK : a ∈ (unitaryCommonFixedSpace X Y)ᗮ) : inner ℂ a b = 0 := by
  have hp := unitaryHeisenberg_project_Y_eq_common X Y Z hrel hYZ a haX haZ
  rw [(unitaryCommonFixedSpace X Y).starProjection_apply_eq_zero_iff.mpr haK] at hp
  calc
    inner ℂ a b = inner ℂ ((unitaryFixedSpace Y).starProjection a) b := by
      rw [(unitaryFixedSpace Y).inner_starProjection_left_eq_right,
        (unitaryFixedSpace Y).starProjection_eq_self_iff.mpr hbY]
    _ = 0 := by rw [hp, inner_zero_left]

theorem unitaryHeisenberg_central_sum_sq_le (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (v u : H) (hv : X v = v) (hu : Y u = u) (huZ : u ∈ (unitaryFixedSpace Z)ᗮ) :
    ‖v + u‖ ^ 2 ≤ (7 / 4 : ℝ) * (‖v‖ ^ 2 + ‖u‖ ^ 2) := by
  have hs := unitaryHeisenberg_angle_sq X Y Z hrel hYZ v u hv hu huZ
  have hn : ‖inner ℂ v u‖ ≤ (3 / 8 : ℝ) * (‖v‖ ^ 2 + ‖u‖ ^ 2) := by
    nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖u‖ ^ 2), sq_nonneg ‖v‖, sq_nonneg ‖u‖,
      norm_nonneg (inner ℂ v u)]
  have hr := (Complex.re_le_norm (inner ℂ v u)).trans hn
  rw [norm_add_sq (𝕜 := ℂ)]
  change ‖v‖ ^ 2 + 2 * (inner ℂ v u).re + ‖u‖ ^ 2 ≤ _
  linarith

theorem unitaryHeisenberg_refined_four_sum (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z) (hXZ : Commute X Z)
    (a b c d : H) (haX : X a = a) (haZ : Z a = a) (hbY : Y b = b) (hbZ : Z b = b)
    (hcX : X c = c) (hdY : Y d = d)
    (haK : a ∈ (unitaryCommonFixedSpace X Y)ᗮ) (hcK : c ∈ (unitaryCommonFixedSpace X Y)ᗮ) :
    ‖a + b + c + d‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
      (1 / 4 : ℝ) * (‖(unitaryFixedSpace Z)ᗮ.starProjection c‖ ^ 2 +
        ‖(unitaryFixedSpace Z)ᗮ.starProjection d‖ ^ 2) := by
  let K := unitaryCommonFixedSpace X Y
  let C := unitaryFixedSpace Z
  let P := C.starProjection
  let Q := Cᗮ.starProjection
  have haP : P a = a := C.starProjection_eq_self_iff.mpr haZ
  have hbP : P b = b := C.starProjection_eq_self_iff.mpr hbZ
  have haQ : Q a = 0 := by
    change Cᗮ.starProjection a = 0
    rw [Submodule.starProjection_orthogonal_val, haP, sub_self]
  have hbQ : Q b = 0 := by
    change Cᗮ.starProjection b = 0
    rw [Submodule.starProjection_orthogonal_val, hbP, sub_self]
  have hPc : P c ∈ Kᗮ := by
    apply K.starProjection_apply_eq_zero_iff.mp
    rw [unitaryHeisenberg_common_project_center X Y Z hrel]
    exact K.starProjection_apply_eq_zero_iff.mpr hcK
  have hA : X (a + P c) = a + P c := by
    rw [map_add, haX, unitaryFixedSpace_projection_commute X Z hXZ, hcX]
  have hAZ : Z (a + P c) = a + P c := by
    rw [map_add, haZ]
    exact congrArg (a + ·) (C.starProjection_apply_mem c : Z (P c) = P c)
  have hB : Y (b + P d) = b + P d := by
    rw [map_add, hbY, unitaryFixedSpace_projection_commute Y Z hYZ, hdY]
  have horth := unitaryHeisenberg_mixed_residual_orthogonal X Y Z hrel hYZ
    (a + P c) (b + P d) hA hAZ hB (Kᗮ.add_mem haK hPc)
  have hPsum : P (a + b + c + d) = (a + P c) + (b + P d) := by
    rw [map_add, map_add, map_add, haP, hbP]
    abel
  have hQsum : Q (a + b + c + d) = Q c + Q d := by
    simp only [map_add, haQ, hbQ, zero_add]
  have hQc : X (Q c) = Q c := by
    change X (Cᗮ.starProjection c) = Cᗮ.starProjection c
    rw [Submodule.starProjection_orthogonal_val, map_sub,
      unitaryFixedSpace_projection_commute X Z hXZ, hcX]
  have hQd : Y (Q d) = Q d := by
    change Y (Cᗮ.starProjection d) = Cᗮ.starProjection d
    rw [Submodule.starProjection_orthogonal_val, map_sub,
      unitaryFixedSpace_projection_commute Y Z hYZ, hdY]
  have hsmall := unitaryHeisenberg_central_sum_sq_le X Y Z hrel hYZ
    (Q c) (Q d) hQc hQd (Cᗮ.starProjection_apply_mem d)
  have hgeom := C.norm_sq_eq_add_norm_sq_starProjection (a + b + c + d)
  change ‖a + b + c + d‖ ^ 2 = ‖P (a + b + c + d)‖ ^ 2 + ‖Q (a + b + c + d)‖ ^ 2 at hgeom
  rw [hPsum, hQsum, norm_add_sq (𝕜 := ℂ) (a + P c) (b + P d), horth, map_zero] at hgeom
  have hc := C.norm_sq_eq_add_norm_sq_starProjection c
  have hd := C.norm_sq_eq_add_norm_sq_starProjection d
  change ‖c‖ ^ 2 = ‖P c‖ ^ 2 + ‖Q c‖ ^ 2 at hc
  change ‖d‖ ^ 2 = ‖P d‖ ^ 2 + ‖Q d‖ ^ 2 at hd
  have h₁ := hilbert_two_vector_sum_sq_le a (P c)
  have h₂ := hilbert_two_vector_sum_sq_le b (P d)
  change ‖a + b + c + d‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
    (1 / 4 : ℝ) * (‖Q c‖ ^ 2 + ‖Q d‖ ^ 2)
  linarith

end ThomGame.Analysis
