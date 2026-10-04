module

public import ThomGame.Analysis.HilbertInvariantProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! Actual fixed spaces and their orthogonal projections for individual unitary operators. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def unitaryFixedSpace (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ H :=
  (U : H →L[ℂ] H).eqLocus 1

theorem mem_unitaryFixedSpace (U : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    ξ ∈ unitaryFixedSpace U ↔ U ξ = ξ := Iff.rfl

theorem unitaryFixedSpace_map (U V : H ≃ₗᵢ[ℂ] H) (hUV : Commute U V) :
    (unitaryFixedSpace V).map U.toLinearEquiv.toLinearMap = unitaryFixedSpace V := by
  have hcomm (ξ : H) : U (V ξ) = V (U ξ) := congrArg (fun W : H ≃ₗᵢ[ℂ] H => W ξ) hUV.eq
  apply le_antisymm
  · rintro ξ ⟨η, hη, rfl⟩
    change V (U η) = U η
    rw [← hcomm, (mem_unitaryFixedSpace V η).mp hη]
  · intro ξ hξ
    refine ⟨U.symm ξ, ?_, U.apply_symm_apply ξ⟩
    change V (U.symm ξ) = U.symm ξ
    apply U.injective
    rw [hcomm, U.apply_symm_apply, (mem_unitaryFixedSpace V ξ).mp hξ]

variable [CompleteSpace H]

instance (U : H ≃ₗᵢ[ℂ] H) : CompleteSpace (unitaryFixedSpace U) :=
  (show IsClosed (unitaryFixedSpace U : Set H) from
    isClosed_eq U.continuous continuous_id).completeSpace_coe

theorem unitaryFixedSpace_projection_commute (U V : H ≃ₗᵢ[ℂ] H) (hUV : Commute U V) (ξ : H) :
    U ((unitaryFixedSpace V).starProjection ξ) = (unitaryFixedSpace V).starProjection (U ξ) := by
  have h := Submodule.starProjection_map_apply U (unitaryFixedSpace V) (U ξ)
  simpa only [unitaryFixedSpace_map U V hUV, U.symm_apply_apply] using h.symm

theorem unitaryFixedSpace_projection_apply (U : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    (unitaryFixedSpace U).starProjection (U ξ) = (unitaryFixedSpace U).starProjection ξ := by
  rw [← unitaryFixedSpace_projection_commute U U (Commute.refl U)]
  exact (unitaryFixedSpace U).starProjection_apply_mem ξ

theorem unitaryFixedSpace_projection_symm_apply (U : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    (unitaryFixedSpace U).starProjection (U.symm ξ) = (unitaryFixedSpace U).starProjection ξ := by
  have h := unitaryFixedSpace_projection_apply U (U.symm ξ)
  rw [U.apply_symm_apply] at h
  exact h.symm

end ThomGame.Analysis
