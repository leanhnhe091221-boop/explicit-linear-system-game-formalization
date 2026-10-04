module

public import ThomGame.Analysis.CStarClampTails
public import ThomGame.Analysis.PositiveTracialProducts

/-!
# Self-adjoint clipping decreases squared trace distance to a bounded target

The two removed positive tails are supported where the clipped element
equals an endpoint. Positivity of the trace on products gives the
projection inequality; expanding the square yields the distance bound.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem trace_clamp_cross_nonneg (τ : A →ₗ[ℝ] ℝ)
    (hpos : ∀ a : A, 0 ≤ a → 0 ≤ τ a) (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (K : ℝ) (hK : 0 ≤ K) (a t : A) (ha : IsSelfAdjoint a) (ht : IsSelfAdjoint t)
    (hbound : ‖t‖ ≤ K) : 0 ≤ τ ((a - cstarNormClamp K a) * (cstarNormClamp K a - t)) := by
  have hu : t ≤ algebraMap ℝ A K := by
    refine le_algebraMap_of_spectrum_le ?_ ht
    intro r hr
    exact (Real.le_norm_self r).trans
      ((IsometricContinuousFunctionalCalculus.norm_spectrum_le t hr ht).trans hbound)
  have hl : -(algebraMap ℝ A K) ≤ t := by
    have hneg : -t ≤ algebraMap ℝ A K := by
      refine le_algebraMap_of_spectrum_le ?_ ht.neg
      intro r hr
      exact (Real.le_norm_self r).trans
        ((IsometricContinuousFunctionalCalculus.norm_spectrum_le (-t) hr ht.neg).trans (by simpa using hbound))
    exact neg_le.mp hneg
  have hp := positive_trace_mul_nonneg τ hpos hcyc (cstarUpperTail K a)
    (algebraMap ℝ A K - t) (cstarUpperTail_nonneg K a) (sub_nonneg.mpr hu)
  have hn := positive_trace_mul_nonneg τ hpos hcyc (cstarLowerTail K a)
    (algebraMap ℝ A K + t) (cstarLowerTail_nonneg K a)
    (by have hh := neg_le_iff_add_nonneg.mp hl; simpa only [add_comm] using hh)
  have he : (a - cstarNormClamp K a) * (cstarNormClamp K a - t) =
      cstarUpperTail K a * (algebraMap ℝ A K - t) +
      cstarLowerTail K a * (algebraMap ℝ A K + t) := by
    rw [cstarNormClamp_tail_sub K hK a ha, sub_mul, mul_sub, mul_sub,
      cstarUpperTail_mul_clamp K hK a, cstarLowerTail_mul_clamp K hK a]
    simp only [mul_sub, mul_add, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, neg_smul]
    abel
  rw [he, map_add]
  exact add_nonneg hp hn

theorem trace_clamp_sq_sub_le (τ : A →ₗ[ℝ] ℝ)
    (hpos : ∀ a : A, 0 ≤ a → 0 ≤ τ a) (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (K : ℝ) (hK : 0 ≤ K) (a t : A) (ha : IsSelfAdjoint a) (ht : IsSelfAdjoint t)
    (hbound : ‖t‖ ≤ K) :
    τ ((cstarNormClamp K a - t) * (cstarNormClamp K a - t)) ≤ τ ((a - t) * (a - t)) := by
  have hc := trace_clamp_cross_nonneg τ hpos hcyc K hK a t ha ht hbound
  have hp := hpos ((a - cstarNormClamp K a) * (a - cstarNormClamp K a))
    ((ha.sub (cstarNormClamp_selfAdjoint K a)).mul_self_nonneg)
  have he : (a - t) * (a - t) =
      (a - cstarNormClamp K a) * (a - cstarNormClamp K a) +
      (cstarNormClamp K a - t) * (cstarNormClamp K a - t) +
      (a - cstarNormClamp K a) * (cstarNormClamp K a - t) +
      (cstarNormClamp K a - t) * (a - cstarNormClamp K a) := by noncomm_ring
  rw [he, map_add, map_add, map_add, hcyc (cstarNormClamp K a - t) (a - cstarNormClamp K a)]
  linarith

end ThomGame.Analysis
