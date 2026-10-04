module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Analysis.Convex.Combination

/-!
# Mean ergodic projections preserve invariant closed convex sets

Cesaro averages of a contraction converge to its actual fixed-space
orthogonal projection. A closed real convex set invariant under the
contraction is therefore invariant under that projection as well.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def meanProjection (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (T.eqLocus (1 : H →L[ℂ] H)).starProjection

theorem meanProjection_norm_le (T : H →L[ℂ] H) : ‖meanProjection T‖ ≤ 1 :=
  (T.eqLocus (1 : H →L[ℂ] H)).starProjection_norm_le

theorem meanProjection_fixed (T : H →L[ℂ] H) (ξ : H) : T (meanProjection T ξ) = meanProjection T ξ :=
  (T.eqLocus (1 : H →L[ℂ] H)).starProjection_apply_mem ξ

theorem meanProjection_eq_self_iff (T : H →L[ℂ] H) (ξ : H) : meanProjection T ξ = ξ ↔ T ξ = ξ :=
  (T.eqLocus (1 : H →L[ℂ] H)).starProjection_eq_self_iff

theorem meanProjection_tendsto (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (ξ : H) :
    Tendsto (fun n => birkhoffAverage ℂ T _root_.id n ξ) atTop (𝓝 (meanProjection T ξ)) :=
  T.tendsto_birkhoffAverage_orthogonalProjection hT ξ

omit [CompleteSpace H] in
theorem birkhoffAverage_mem_invariant_convex (T : H →L[ℂ] H) (S : Set H)
    (hconv : Convex ℝ S) (hinv : Set.MapsTo T S S) (ξ : H) (hξ : ξ ∈ S) (n : Nat) (hn : 0 < n) :
    birkhoffAverage ℂ T _root_.id n ξ ∈ S := by
  have hi (j : Nat) : (T : H → H)^[j] ξ ∈ S := by
    induction j with
    | zero => exact hξ
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact hinv ih
  have hw : ∑ _j ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  have hm := hconv.sum_mem (t := Finset.range n) (w := fun _ => (n : ℝ)⁻¹)
    (z := fun j => (T : H → H)^[j] ξ)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)) hw (fun j _ => hi j)
  simpa only [birkhoffAverage, birkhoffSum, Function.id_def, ← Finset.smul_sum,
    ← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using hm

theorem meanProjection_mem_invariant_closed_convex (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (S : Set H) (hclosed : IsClosed S) (hconv : Convex ℝ S) (hinv : Set.MapsTo T S S)
    (ξ : H) (hξ : ξ ∈ S) : meanProjection T ξ ∈ S := by
  apply hclosed.mem_of_tendsto (meanProjection_tendsto T hT ξ)
  filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
  exact birkhoffAverage_mem_invariant_convex T S hconv hinv ξ hξ n hn

end ThomGame.Analysis
