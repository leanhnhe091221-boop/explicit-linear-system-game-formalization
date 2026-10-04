module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Vector-state perturbation estimates for actual bounded Hilbert-space operators. -/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertVectorState_sub_identity (T : H →L[ℂ] H) (x y : H) :
    inner ℂ x (T x) - inner ℂ y (T y) =
      inner ℂ (x - y) (T x) + inner ℂ y (T (x - y)) := by
  rw [map_sub, inner_sub_left, inner_sub_right]
  abel

theorem hilbertVectorState_sub_norm_le (T : H →L[ℂ] H) (x y : H) :
    ‖inner ℂ x (T x) - inner ℂ y (T y)‖ ≤
      ‖T‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [hilbertVectorState_sub_identity]
  calc
    ‖inner ℂ (x - y) (T x) + inner ℂ y (T (x - y))‖ ≤
        ‖inner ℂ (x - y) (T x)‖ + ‖inner ℂ y (T (x - y))‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖T x‖ + ‖y‖ * ‖T (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * (‖T‖ * ‖x‖) + ‖y‖ * (‖T‖ * ‖x - y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (T.le_opNorm (x - y)) (norm_nonneg _))
    _ = ‖T‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

theorem hilbertVectorState_re_sub_abs_le (T : H →L[ℂ] H) (x y : H) :
    |(inner ℂ x (T x)).re - (inner ℂ y (T y)).re| ≤
      ‖T‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  exact (Complex.abs_re_le_norm (inner ℂ x (T x) - inner ℂ y (T y))).trans
    (hilbertVectorState_sub_norm_le T x y)

theorem hilbertVectorState_unit_contraction_bound (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖inner ℂ x (T x) - inner ℂ y (T y)‖ ≤ 2 * ‖x - y‖ := by
  have h := hilbertVectorState_sub_norm_le T x y
  rw [hx, hy] at h
  calc
    ‖inner ℂ x (T x) - inner ℂ y (T y)‖ ≤ ‖T‖ * (1 + 1) * ‖x - y‖ := h
    _ ≤ 1 * (1 + 1) * ‖x - y‖ := by gcongr
    _ = 2 * ‖x - y‖ := by ring

theorem hilbertVectorState_unit_contraction_re_bound (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |(inner ℂ x (T x)).re - (inner ℂ y (T y)).re| ≤ 2 * ‖x - y‖ := by
  exact (Complex.abs_re_le_norm (inner ℂ x (T x) - inner ℂ y (T y))).trans
    (hilbertVectorState_unit_contraction_bound T hT x y hx hy)

end ThomGame.Analysis
