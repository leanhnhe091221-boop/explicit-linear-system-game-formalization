module

public import ThomGame.Analysis.IntegerHeisenbergUnitaryAngle
public import ThomGame.Analysis.InvariantMeanProjection

/-! The four-edge local codistance estimate for genuine integer Heisenberg operators. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryHeisenberg_mixed_fixed_orthogonal (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (hcommon : ∀ w : H, X w = w → Y w = w → w = 0)
    (a b : H) (haX : X a = a) (haZ : Z a = a) (hbY : Y b = b) : inner ℂ a b = 0 := by
  let S := unitaryFixedSpace X ⊓ unitaryFixedSpace Z
  have hclosed : IsClosed (S : Set H) :=
    (isClosed_eq X.continuous continuous_id).inter (isClosed_eq Z.continuous continuous_id)
  have hconv : Convex ℝ (S : Set H) := (S.restrictScalars ℝ).convex
  have hinv : Set.MapsTo (Y : H →L[ℂ] H) (S : Set H) (S : Set H) := by
    intro w hw
    rcases hw with ⟨hwX, hwZ⟩
    change X w = w at hwX
    change Z w = w at hwZ
    have hcomm : Z (Y w) = Y (Z w) := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hYZ.symm.eq
    constructor
    · change X (Y w) = Y w
      have h := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hrel
      change Y (X w) = X (Z (Y w)) at h
      rw [hwX, hcomm, hwZ] at h
      exact h.symm
    · change Z (Y w) = Y w
      rw [hcomm, hwZ]
  have hnorm : ‖(Y : H →L[ℂ] H)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖Y w‖ ≤ 1 * ‖w‖
    rw [Y.norm_map, one_mul]
  have hP := meanProjection_mem_invariant_closed_convex (Y : H →L[ℂ] H) hnorm
    (S : Set H) hclosed hconv hinv a ⟨haX, haZ⟩
  have hzero := hcommon (meanProjection (Y : H →L[ℂ] H) a) hP.1
    (meanProjection_fixed (Y : H →L[ℂ] H) a)
  change (unitaryFixedSpace Y).starProjection a = 0 at hzero
  calc
    inner ℂ a b = inner ℂ ((unitaryFixedSpace Y).starProjection a) b := by
      rw [(unitaryFixedSpace Y).inner_starProjection_left_eq_right,
        (unitaryFixedSpace Y).starProjection_eq_self_iff.mpr hbY]
    _ = 0 := by rw [hzero, inner_zero_left]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem hilbert_two_vector_sum_sq_le (a b : H) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem unitaryHeisenberg_four_sum_sq_le (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z) (hXZ : Commute X Z)
    (hcommon : ∀ w : H, X w = w → Y w = w → w = 0)
    (a b c d : H) (haX : X a = a) (haZ : Z a = a) (hbY : Y b = b) (hbZ : Z b = b)
    (hcX : X c = c) (hdY : Y d = d) :
    ‖a + b + c + d‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  let K := unitaryFixedSpace Z
  let P := K.starProjection
  let Q := Kᗮ.starProjection
  have haP : P a = a := K.starProjection_eq_self_iff.mpr haZ
  have hbP : P b = b := K.starProjection_eq_self_iff.mpr hbZ
  have haQ : Q a = 0 := by
    change Kᗮ.starProjection a = 0
    rw [Submodule.starProjection_orthogonal_val, haP, sub_self]
  have hbQ : Q b = 0 := by
    change Kᗮ.starProjection b = 0
    rw [Submodule.starProjection_orthogonal_val, hbP, sub_self]
  have hA : X (a + P c) = a + P c := by
    rw [map_add, haX, unitaryFixedSpace_projection_commute X Z hXZ, hcX]
  have hAZ : Z (a + P c) = a + P c := by
    rw [map_add, haZ]
    exact congrArg (a + ·) (K.starProjection_apply_mem c : Z (P c) = P c)
  have hB : Y (b + P d) = b + P d := by
    rw [map_add, hbY, unitaryFixedSpace_projection_commute Y Z hYZ, hdY]
  have horth := unitaryHeisenberg_mixed_fixed_orthogonal X Y Z hrel hYZ hcommon
    (a + P c) (b + P d) hA hAZ hB
  have hPsum : P (a + b + c + d) = (a + P c) + (b + P d) := by
    rw [map_add, map_add, map_add, haP, hbP]
    abel
  have hQsum : Q (a + b + c + d) = Q c + Q d := by
    simp only [map_add, haQ, hbQ, zero_add]
  have hgeom := K.norm_sq_eq_add_norm_sq_starProjection (a + b + c + d)
  change ‖a + b + c + d‖ ^ 2 = ‖P (a + b + c + d)‖ ^ 2 + ‖Q (a + b + c + d)‖ ^ 2 at hgeom
  rw [hPsum, hQsum, norm_add_sq (𝕜 := ℂ) (a + P c) (b + P d), horth, map_zero] at hgeom
  have hc := K.norm_sq_eq_add_norm_sq_starProjection c
  have hd := K.norm_sq_eq_add_norm_sq_starProjection d
  change ‖c‖ ^ 2 = ‖P c‖ ^ 2 + ‖Q c‖ ^ 2 at hc
  change ‖d‖ ^ 2 = ‖P d‖ ^ 2 + ‖Q d‖ ^ 2 at hd
  have h₁ := hilbert_two_vector_sum_sq_le a (P c)
  have h₂ := hilbert_two_vector_sum_sq_le b (P d)
  have h₃ := hilbert_two_vector_sum_sq_le (Q c) (Q d)
  nlinarith

end ThomGame.Analysis
