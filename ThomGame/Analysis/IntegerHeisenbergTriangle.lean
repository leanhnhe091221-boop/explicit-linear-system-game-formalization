module

public import ThomGame.Analysis.IntegerHeisenbergLocalCodistance

/-! Exact triangle projection identities for integer Heisenberg unitary operators. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryCommonFixedSpace (X Y : H ≃ₗᵢ[ℂ] H) : Submodule ℂ H :=
  unitaryFixedSpace X ⊓ unitaryFixedSpace Y

instance unitaryCommonFixedSpace_complete (X Y : H ≃ₗᵢ[ℂ] H) :
    CompleteSpace (unitaryCommonFixedSpace X Y) :=
  ((isClosed_eq X.continuous continuous_id).inter
    (isClosed_eq Y.continuous continuous_id)).completeSpace_coe

theorem unitaryFixedSpace_projection_mem_of_mapsTo (U : H ≃ₗᵢ[ℂ] H) (S : Submodule ℂ H)
    (hclosed : IsClosed (S : Set H)) (hinv : Set.MapsTo U S S) (a : H) (ha : a ∈ S) :
    (unitaryFixedSpace U).starProjection a ∈ S := by
  have hnorm : ‖(U : H →L[ℂ] H)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖U w‖ ≤ 1 * ‖w‖
    rw [U.norm_map, one_mul]
  exact meanProjection_mem_invariant_closed_convex (U : H →L[ℂ] H) hnorm
    (S : Set H) hclosed (S.restrictScalars ℝ).convex hinv a ha

theorem unitaryHeisenberg_project_Y_eq_common (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (b : H) (hbX : X b = b) (hbZ : Z b = b) :
    (unitaryFixedSpace Y).starProjection b = (unitaryCommonFixedSpace X Y).starProjection b := by
  let S := unitaryFixedSpace X ⊓ unitaryFixedSpace Z
  have hclosed : IsClosed (S : Set H) :=
    (isClosed_eq X.continuous continuous_id).inter (isClosed_eq Z.continuous continuous_id)
  have hinv : Set.MapsTo Y S S := by
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
  have hmem := unitaryFixedSpace_projection_mem_of_mapsTo Y S hclosed hinv b ⟨hbX, hbZ⟩
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨hmem.1, (unitaryFixedSpace Y).starProjection_apply_mem b⟩
  · exact Submodule.orthogonal_le
      (show unitaryCommonFixedSpace X Y ≤ unitaryFixedSpace Y from inf_le_right)
      ((unitaryFixedSpace Y).sub_starProjection_mem_orthogonal b)

theorem unitaryHeisenberg_project_X_eq_common (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hXZ : Commute X Z)
    (a : H) (haY : Y a = a) (haZ : Z a = a) :
    (unitaryFixedSpace X).starProjection a = (unitaryCommonFixedSpace X Y).starProjection a := by
  let S := unitaryFixedSpace Y ⊓ unitaryFixedSpace Z
  have hclosed : IsClosed (S : Set H) :=
    (isClosed_eq Y.continuous continuous_id).inter (isClosed_eq Z.continuous continuous_id)
  have hinv : Set.MapsTo X S S := by
    intro w hw
    rcases hw with ⟨hwY, hwZ⟩
    change Y w = w at hwY
    change Z w = w at hwZ
    constructor
    · change Y (X w) = X w
      have h := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hrel
      change Y (X w) = X (Z (Y w)) at h
      simpa only [hwY, hwZ] using h
    · change Z (X w) = X w
      have h := congrArg (fun U : H ≃ₗᵢ[ℂ] H => U w) hXZ.symm.eq
      change Z (X w) = X (Z w) at h
      simpa only [hwZ] using h
  have hmem := unitaryFixedSpace_projection_mem_of_mapsTo X S hclosed hinv a ⟨haY, haZ⟩
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(unitaryFixedSpace X).starProjection_apply_mem a, hmem.1⟩
  · exact Submodule.orthogonal_le
      (show unitaryCommonFixedSpace X Y ≤ unitaryFixedSpace X from inf_le_left)
      ((unitaryFixedSpace X).sub_starProjection_mem_orthogonal a)

theorem unitaryHeisenberg_triangle_residual_orthogonal (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z)
    (a b : H) (haY : Y a = a) (hbX : X b = b) (hbZ : Z b = b) :
    inner ℂ (a - (unitaryCommonFixedSpace X Y).starProjection a)
      (b - (unitaryCommonFixedSpace X Y).starProjection b) = 0 := by
  have ha : a - (unitaryCommonFixedSpace X Y).starProjection a ∈ unitaryFixedSpace Y :=
    (unitaryFixedSpace Y).sub_mem haY ((unitaryCommonFixedSpace X Y).starProjection_apply_mem a).2
  rw [← unitaryHeisenberg_project_Y_eq_common X Y Z hrel hYZ b hbX hbZ]
  exact (Submodule.mem_orthogonal _ _).mp
    ((unitaryFixedSpace Y).sub_starProjection_mem_orthogonal b) _ ha

theorem unitaryHeisenberg_triangle_energy (X Y Z : H ≃ₗᵢ[ℂ] H)
    (hrel : Y * X = X * Z * Y) (hYZ : Commute Y Z) (hXZ : Commute X Z)
    (a b : H) (haY : Y a = a) (haZ : Z a = a) (hbX : X b = b) (hbZ : Z b = b) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖a + b‖ ^ 2 ≤
      5 * (‖(unitaryCommonFixedSpace X Y).starProjection a‖ ^ 2 +
        ‖(unitaryCommonFixedSpace X Y).starProjection b‖ ^ 2) +
      3 * (‖(unitaryFixedSpace X)ᗮ.starProjection (a + b)‖ ^ 2 +
        ‖(unitaryFixedSpace Y)ᗮ.starProjection (a + b)‖ ^ 2) := by
  let K := unitaryCommonFixedSpace X Y
  have hXa := unitaryHeisenberg_project_X_eq_common X Y Z hrel hXZ a haY haZ
  have hYb := unitaryHeisenberg_project_Y_eq_common X Y Z hrel hYZ b hbX hbZ
  have hX : (unitaryFixedSpace X)ᗮ.starProjection (a + b) = a - K.starProjection a := by
    rw [Submodule.starProjection_orthogonal_val, map_add, hXa,
      (unitaryFixedSpace X).starProjection_eq_self_iff.mpr hbX]
    abel
  have hY : (unitaryFixedSpace Y)ᗮ.starProjection (a + b) = b - K.starProjection b := by
    rw [Submodule.starProjection_orthogonal_val, map_add, hYb,
      (unitaryFixedSpace Y).starProjection_eq_self_iff.mpr haY]
    abel
  have horth := unitaryHeisenberg_triangle_residual_orthogonal X Y Z hrel hYZ a b haY hbX hbZ
  have hsum : ‖a + b‖ ^ 2 = ‖K.starProjection (a + b)‖ ^ 2 +
      ‖a - K.starProjection a‖ ^ 2 + ‖b - K.starProjection b‖ ^ 2 := by
    have h := K.norm_sq_eq_add_norm_sq_starProjection (a + b)
    rw [Submodule.starProjection_orthogonal_val, map_add] at h
    have hab : a + b - (K.starProjection a + K.starProjection b) =
        (a - K.starProjection a) + (b - K.starProjection b) := by abel
    rw [hab, norm_add_sq (𝕜 := ℂ) (a - K.starProjection a) (b - K.starProjection b), horth, map_zero] at h
    simpa only [map_add, mul_zero, add_zero, add_assoc] using h
  have hp := hilbert_two_vector_sum_sq_le (K.starProjection a) (K.starProjection b)
  rw [← map_add] at hp
  have hpa := K.norm_sq_eq_add_norm_sq_starProjection a
  have hpb := K.norm_sq_eq_add_norm_sq_starProjection b
  rw [Submodule.starProjection_orthogonal_val] at hpa hpb
  rw [hX, hY]
  change ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖a + b‖ ^ 2 ≤
    5 * (‖K.starProjection a‖ ^ 2 + ‖K.starProjection b‖ ^ 2) +
    3 * (‖a - K.starProjection a‖ ^ 2 + ‖b - K.starProjection b‖ ^ 2)
  linarith

end ThomGame.Analysis
