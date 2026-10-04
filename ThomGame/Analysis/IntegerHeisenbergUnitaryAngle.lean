module

public import ThomGame.Analysis.UnitaryFixedSpaceProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The integer Heisenberg angle on the orthogonal complement of central fixed vectors. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryHeisenberg_projected_inverse_fixed (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (v : H) (hv : Y v = v) :
    (unitaryFixedSpace Y).starProjection (X.symm v) ∈ unitaryFixedSpace Z := by
  have hcomm (w : H) : Y (Z w) = Z (Y w) := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hYZ.eq
  have happly (w : H) : Y (X w) = X (Z (Y w)) :=
    congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hrel
  have hzw : Z (X.symm v) = Y.symm (X.symm v) := by
    apply Y.injective
    rw [Y.apply_symm_apply, hcomm]
    apply X.injective
    rw [← happly, X.apply_symm_apply, hv]
  change Z ((unitaryFixedSpace Y).starProjection (X.symm v)) =
    (unitaryFixedSpace Y).starProjection (X.symm v)
  rw [unitaryFixedSpace_projection_commute Z Y hYZ.symm, hzw,
    unitaryFixedSpace_projection_symm_apply]

theorem unitaryHeisenberg_translate_orthogonal (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (u : H) (hu : Y u = u) (huZ : u ∈ (unitaryFixedSpace Z)ᗮ) :
    X u ∈ (unitaryFixedSpace Y)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  have hp := unitaryHeisenberg_projected_inverse_fixed X Y Z hrel hYZ v hv
  have hzero := (Submodule.mem_orthogonal _ _).mp huZ
    ((unitaryFixedSpace Y).starProjection (X.symm v)) hp
  rw [(unitaryFixedSpace Y).inner_starProjection_left_eq_right,
    (unitaryFixedSpace Y).starProjection_eq_self_iff.mpr hu] at hzero
  calc
    inner ℂ v (X u) = inner ℂ (X (X.symm v)) (X u) := by rw [X.apply_symm_apply]
    _ = inner ℂ (X.symm v) u := X.inner_map_map _ _
    _ = 0 := hzero

theorem unitaryHeisenberg_angle_sq (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (v u : H) (hv : X v = v) (hu : Y u = u) (huZ : u ∈ (unitaryFixedSpace Z)ᗮ) :
    ‖inner ℂ v u‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  have horth : inner ℂ u (X u) = 0 :=
    (Submodule.mem_orthogonal _ _).mp (unitaryHeisenberg_translate_orthogonal X Y Z hrel hYZ u hu huZ) u hu
  have hnorm : ‖u + X u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), horth, map_zero, X.norm_map]
    ring
  have hinner : inner ℂ v (X u) = inner ℂ v u := by
    conv_lhs => lhs; rw [← hv]
    exact X.inner_map_map v u
  have hcs := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) v (u + X u)) 2
  rw [inner_add_right, hinner, ← two_mul, norm_mul] at hcs
  simp only [mul_pow, hnorm] at hcs
  norm_num at hcs
  nlinarith

theorem unitaryHeisenberg_angle (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (v u : H) (hv : X v = v) (hu : Y u = u) (huZ : u ∈ (unitaryFixedSpace Z)ᗮ) :
    ‖inner ℂ v u‖ ≤ (Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖ := by
  have hs := unitaryHeisenberg_angle_sq X Y Z hrel hYZ v u hv hu huZ
  have he : ((Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖) ^ 2 = (1 / 2 : ℝ) * ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖)).mp
  rwa [he]

end ThomGame.Analysis
