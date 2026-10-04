module

public import ThomGame.Analysis.HilbertCoerciveSurjectivity

/-! Transferring a projection lower bound to the reverse projection. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def subspaceProjection (A B : Submodule ℂ H) [CompleteSpace B] : A →L[ℂ] B :=
  (B.starProjection.comp A.subtypeL).codRestrict B (fun a => B.starProjection_apply_mem a)

theorem subspaceProjection_apply (A B : Submodule ℂ H) [CompleteSpace B] (a : A) :
    (subspaceProjection A B a : H) = B.starProjection a := rfl

theorem subspaceProjection_surjective (A B : Submodule ℂ H) [CompleteSpace A] [CompleteSpace B]
    (c : ℝ) (hc : 0 < c) (hbound : ∀ a ∈ A, c * ‖a‖ ≤ ‖B.starProjection a‖)
    (horth : B ⊓ Aᗮ = ⊥) : Function.Surjective (subspaceProjection A B) := by
  let T := subspaceProjection A B
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro a
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    have h := hbound (a : H) a.property
    change ‖(a : H)‖ ≤ c⁻¹ * ‖B.starProjection (a : H)‖
    have hi : ‖(a : H)‖ ≤ ‖B.starProjection (a : H)‖ / c := (le_div_iff₀ hc).mpr (by nlinarith)
    simpa only [div_eq_inv_mul] using hi
  have hclosed : IsClosed (T.range : Set B) := hanti.isClosed_range T.uniformContinuous
  let := hclosed.completeSpace_coe
  have hR : T.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro w hw
    have hwA : (w : H) ∈ Aᗮ := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro a ha
      have hinner := (Submodule.mem_orthogonal _ _).mp hw (T ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
      change inner ℂ (B.starProjection a) (w : H) = 0 at hinner
      rw [B.inner_starProjection_left_eq_right, B.starProjection_eq_self_iff.mpr w.property] at hinner
      exact hinner
    have hwzero : (w : H) = 0 := by
      have hm : (w : H) ∈ B ⊓ Aᗮ := ⟨w.property, hwA⟩
      rwa [horth, Submodule.mem_bot] at hm
    rw [Submodule.mem_bot]
    exact Subtype.ext hwzero
  have hrange : T.range = ⊤ := by
    rw [← T.range.orthogonal_orthogonal, hR, Submodule.bot_orthogonal_eq_top]
  exact LinearMap.range_eq_top.mp hrange

theorem subspaceProjection_lower_dual (A B : Submodule ℂ H) [CompleteSpace A] [CompleteSpace B]
    (c : ℝ) (hc : 0 < c) (hbound : ∀ a ∈ A, c * ‖a‖ ≤ ‖B.starProjection a‖)
    (horth : B ⊓ Aᗮ = ⊥) (b : H) (hb : b ∈ B) : c * ‖b‖ ≤ ‖A.starProjection b‖ := by
  obtain ⟨a, ha⟩ := subspaceProjection_surjective A B c hc hbound horth ⟨b, hb⟩
  have heq : B.starProjection (a : H) = b := congrArg Subtype.val ha
  have haBound := hbound (a : H) a.property
  rw [heq] at haBound
  have hinner : inner ℂ (a : H) (A.starProjection b) = inner ℂ b b := by
    rw [← A.inner_starProjection_left_eq_right, A.starProjection_eq_self_iff.mpr a.property]
    calc
      inner ℂ (a : H) b = inner ℂ (a : H) (B.starProjection b) := by
        rw [B.starProjection_eq_self_iff.mpr hb]
      _ = inner ℂ (B.starProjection (a : H)) b := (B.inner_starProjection_left_eq_right _ _).symm
      _ = inner ℂ b b := by rw [heq]
  have hcs := re_inner_le_norm (𝕜 := ℂ) (a : H) (A.starProjection b)
  rw [hinner, inner_self_eq_norm_sq] at hcs
  have hmul₁ := mul_le_mul_of_nonneg_left hcs hc.le
  have hmul₂ := mul_le_mul_of_nonneg_right haBound (norm_nonneg (A.starProjection b))
  by_cases hz : b = 0
  · simp [hz]
  have hn := norm_pos_iff.mpr hz
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

end ThomGame.Analysis
