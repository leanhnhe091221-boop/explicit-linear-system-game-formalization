module

public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Operator norm bounds are weak operator closed

The operator norm bound is characterized by real parts of matrix
coefficients between unit vectors. Each coefficient is WOT continuous.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem wot_norm_le_iff (T : H →WOT[ℂ] H) (K : ℝ) (hK : 0 ≤ K) :
    ‖T.toCLM‖ ≤ K ↔ ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 → (inner ℂ y (T x)).re ≤ K := by
  constructor
  · intro h x y hx hy
    calc
      (inner ℂ y (T x)).re ≤ ‖inner ℂ y (T x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (K * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T.toCLM.le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))) (norm_nonneg y)
      _ = K := by rw [hx, hy, one_mul, mul_one]
  · intro h
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le hK
    intro x y hx hy
    rw [inner_re_symm]
    exact h x y hx hy

theorem wot_norm_ball_isClosed (K : ℝ) (hK : 0 ≤ K) :
    IsClosed {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ K} := by
  simp_rw [wot_norm_le_iff _ K hK, Set.ofPred_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_iInter fun _hx => isClosed_iInter fun _hy => ?_
  exact isClosed_le (Complex.continuous_re.comp
    (ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ y))) continuous_const

end ThomGame.Analysis
