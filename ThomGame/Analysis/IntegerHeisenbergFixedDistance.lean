module

public import ThomGame.Analysis.IntegerHeisenbergTriangle

/-! Three actual fixed-space projections produce a vector fixed by a root pair. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryHeisenberg_common_fixed_distance (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z) (hXZ : Commute X Z) (ξ : H) :
    ‖ξ - (unitaryCommonFixedSpace X Y).starProjection ξ‖ ≤
      ‖ξ - (unitaryFixedSpace X).starProjection ξ‖ +
      ‖ξ - (unitaryFixedSpace Y).starProjection ξ‖ +
      ‖ξ - (unitaryFixedSpace Z).starProjection ξ‖ := by
  let K := unitaryCommonFixedSpace X Y
  let PX := (unitaryFixedSpace X).starProjection
  let PY := (unitaryFixedSpace Y).starProjection
  let PZ := (unitaryFixedSpace Z).starProjection
  let z := PX (PZ ξ)
  let y := PY z
  have hzX : X z = z := (unitaryFixedSpace X).starProjection_apply_mem _
  have hzZ : Z z = z := by
    change Z ((unitaryFixedSpace X).starProjection (PZ ξ)) = (unitaryFixedSpace X).starProjection (PZ ξ)
    rw [unitaryFixedSpace_projection_commute Z X hXZ.symm]
    exact congrArg PX ((unitaryFixedSpace Z).starProjection_apply_mem ξ : Z (PZ ξ) = PZ ξ)
  have hy : y ∈ K := by
    change (unitaryFixedSpace Y).starProjection z ∈ K
    rw [unitaryHeisenberg_project_Y_eq_common X Y Z hrel hYZ z hzX hzZ]
    exact K.starProjection_apply_mem z
  have hnear := Kᗮ.norm_starProjection_apply_le (ξ - y)
  rw [Submodule.starProjection_orthogonal_val, map_sub, K.starProjection_eq_self_iff.mpr hy] at hnear
  have hcancel : ξ - y - (K.starProjection ξ - y) = ξ - K.starProjection ξ := by abel
  rw [hcancel] at hnear
  have hX := (unitaryFixedSpace X).norm_starProjection_apply_le (ξ - PZ ξ)
  rw [map_sub] at hX
  have hZ : ‖ξ - z‖ ≤ ‖ξ - PX ξ‖ + ‖ξ - PZ ξ‖ := by
    have ht : ‖ξ - z‖ ≤ ‖ξ - PX ξ‖ + ‖PX ξ - z‖ := by
      simpa only [dist_eq_norm] using dist_triangle ξ (PX ξ) z
    change ‖PX ξ - z‖ ≤ ‖ξ - PZ ξ‖ at hX
    linarith
  have hY := (unitaryFixedSpace Y).norm_starProjection_apply_le (ξ - z)
  rw [map_sub] at hY
  have ht : ‖ξ - y‖ ≤ ‖ξ - PY ξ‖ + ‖PY ξ - y‖ := by
    simpa only [dist_eq_norm] using dist_triangle ξ (PY ξ) y
  change ‖PY ξ - y‖ ≤ ‖ξ - z‖ at hY
  change ‖ξ - K.starProjection ξ‖ ≤ ‖ξ - PX ξ‖ + ‖ξ - PY ξ‖ + ‖ξ - PZ ξ‖
  linarith

end ThomGame.Analysis
