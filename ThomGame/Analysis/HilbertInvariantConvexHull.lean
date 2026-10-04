module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith

/-!
# A common fixed point in an invariant closed convex hull

The unique point of least Hilbert norm is fixed by every norm-preserving
linear map that preserves the original set. No averaging measure is needed.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_mem_closedConvexHull (T : ι → E →L[ℝ] E) (S : Set E) (hne : S.Nonempty)
    (hinv : ∀ i, Set.MapsTo (T i) S S) (hnorm : ∀ i x, ‖T i x‖ = ‖x‖) :
    ∃ y ∈ closedConvexHull ℝ S, ∀ i, T i y = y := by
  let K := closedConvexHull ℝ S
  have hK : ∀ i, Set.MapsTo (T i) K K := by
    intro i
    exact closedConvexHull_min (fun x hx => subset_closedConvexHull (hinv i hx))
      (convex_closedConvexHull.linear_preimage (T i).toLinearMap)
      (isClosed_closedConvexHull.preimage (T i).continuous)
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hne.mono subset_closedConvexHull) isClosed_closedConvexHull.isComplete convex_closedConvexHull (0 : E)
  refine ⟨y, hy, fun i => ?_⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero convex_closedConvexHull hy).mp hmin (T i y) (hK i hy)
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
  have hs := norm_sub_sq_real y (T i y)
  rw [hnorm] at hs
  have hz : ‖y - T i y‖ = 0 := by nlinarith [norm_nonneg (y - T i y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exists_fixed_near_of_invariant_set (T : ι → E →L[ℝ] E) (S : Set E) (hne : S.Nonempty)
    (hinv : ∀ i, Set.MapsTo (T i) S S) (hnorm : ∀ i x, ‖T i x‖ = ‖x‖)
    (x : E) (C : ℝ) (hbound : ∀ z ∈ S, ‖z - x‖ ≤ C) :
    ∃ y ∈ closedConvexHull ℝ S, (∀ i, T i y = y) ∧ ‖y - x‖ ≤ C := by
  obtain ⟨y, hy, hfix⟩ := exists_fixed_mem_closedConvexHull T S hne hinv hnorm
  refine ⟨y, hy, hfix, ?_⟩
  have hb : closedConvexHull ℝ S ⊆ Metric.closedBall x C :=
    closedConvexHull_min (fun z hz => by simpa only [Metric.mem_closedBall, dist_eq_norm] using hbound z hz)
      (convex_closedBall x C) Metric.isClosed_closedBall
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hb hy

end ThomGame.Analysis
