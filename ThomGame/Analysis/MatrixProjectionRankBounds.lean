module

public import ThomGame.Analysis.MatrixProjectionRankSums

/-!
# Positivity and half-rank tests for projections

The trace uses any positive ambient normalization, including when the
projection is supported on a smaller corner.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matrixTraceReal_projection_eq_zero_iff {r : Nat} (hr : 0 < r)
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) : matrixTraceReal r P = 0 ↔ P = 0 := by
  have he : matrixTraceReal r P = rectHSNorm r P ^ 2 := by
    have hh := matrixTraceReal_gram r P
    rwa [hP.isSelfAdjoint.isHermitian.eq, hP.isIdempotentElem.eq] at hh
  rw [he, sq_eq_zero_iff, rectHSNorm_eq_zero_iff hr]

theorem matrixTraceReal_projection_pos {r : Nat} (hr : 0 < r)
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (hne : P ≠ 0) : 0 < matrixTraceReal r P := by
  have hz := matrixTraceReal_nonneg r hP.nonneg
  by_contra hh
  exact hne ((matrixTraceReal_projection_eq_zero_iff hr hP).mp (le_antisymm (not_lt.mp hh) hz))

theorem matrixProjection_rank_pos {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (hne : P ≠ 0) :
    0 < P.rank := by
  have hp := matrixTraceReal_projection_pos (by decide : 0 < 1) hP hne
  rw [matrixTraceReal_projection_rank 1 hP, Nat.cast_one, div_one] at hp
  exact_mod_cast hp

theorem matrixProjection_trace_le_half_iff {r : Nat} (hr : 0 < r)
    {P Q : Matrix ι ι ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    matrixTraceReal r P ≤ matrixTraceReal r Q / 2 ↔ 2 * P.rank ≤ Q.rank := by
  have hd : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have he : 2 * matrixTraceReal r P ≤ matrixTraceReal r Q ↔ 2 * P.rank ≤ Q.rank := by
    rw [matrixTraceReal_projection_rank r hP, matrixTraceReal_projection_rank r hQ,
      ← mul_div_assoc, div_le_div_iff_of_pos_right hd]
    norm_cast
  constructor
  · intro hh
    exact he.mp (by linarith only [hh])
  · intro hh
    have hh' := he.mpr hh
    linarith only [hh']

theorem matrixProjection_rank_sub_lt {P Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hle : Q ≤ P) (hne : Q ≠ 0) :
    (P - Q).rank < P.rank := by
  have hr := matrixProjection_rank_sub_add hP hQ hle
  have hq := matrixProjection_rank_pos hQ hne
  omega

end ThomGame.Analysis
