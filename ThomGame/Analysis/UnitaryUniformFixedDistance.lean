module

public import ThomGame.Analysis.IntegerHeisenbergTriangle

/-! Uniform displacement of all powers bounds the distance to the actual fixed space. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryFixedSpace_uniform_distance (U : H ≃ₗᵢ[ℂ] H) (ξ : H) (ε : ℝ)
    (hmove : ∀ n : ℕ, ‖(U ^ n) ξ - ξ‖ ≤ ε) :
    ‖ξ - (unitaryFixedSpace U).starProjection ξ‖ ≤ ε := by
  have hnorm : ‖(U : H →L[ℂ] H)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖U w‖ ≤ 1 * ‖w‖
    rw [U.norm_map, one_mul]
  have hi (n : ℕ) : ((U : H →L[ℂ] H) : H → H)^[n] ξ = (U ^ n) ξ := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ']
        rfl
  have hav (n : ℕ) (hn : 0 < n) :
      birkhoffAverage ℂ (U : H →L[ℂ] H) _root_.id n ξ ∈ Metric.closedBall ξ ε := by
    have hw : ∑ _j ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    have hm := (convex_closedBall ξ ε).sum_mem (t := Finset.range n)
      (w := fun _ => (n : ℝ)⁻¹) (z := fun j => ((U : H →L[ℂ] H) : H → H)^[j] ξ)
      (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)) hw (fun j _ => by
        rw [Metric.mem_closedBall, dist_eq_norm, hi]
        exact hmove j)
    simpa only [birkhoffAverage, birkhoffSum, Function.id_def, ← Finset.smul_sum,
      ← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using hm
  have hp : meanProjection (U : H →L[ℂ] H) ξ ∈ Metric.closedBall ξ ε := by
    apply (Metric.isClosed_closedBall : IsClosed (Metric.closedBall ξ ε)).mem_of_tendsto
      (meanProjection_tendsto (U : H →L[ℂ] H) hnorm ξ)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hav n hn
  change (unitaryFixedSpace U).starProjection ξ ∈ Metric.closedBall ξ ε at hp
  simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hp

end ThomGame.Analysis
