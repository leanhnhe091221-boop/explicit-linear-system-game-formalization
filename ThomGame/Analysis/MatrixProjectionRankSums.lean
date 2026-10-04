module

public import ThomGame.Analysis.MatrixProjectionSubrank
public import Mathlib.RingTheory.Idempotents

/-!
# Ranks of orthogonal sums and nested projection differences
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

theorem matrixProjection_sum (P : μ → Matrix ι ι ℂ) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) : IsStarProjection (∑ i, P i) := by
  refine ⟨(OrthogonalIdempotents.mk (fun i => (hP i).isIdempotentElem) horth).isIdempotentElem_sum, ?_⟩
  change star (∑ i, P i) = ∑ i, P i
  simp only [star_sum, fun i => (hP i).isSelfAdjoint.star_eq]

theorem matrixProjection_sum_rank (P : μ → Matrix ι ι ℂ) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) : (∑ i, P i).rank = ∑ i, (P i).rank := by
  have he := matrixTraceReal_sum 1 Finset.univ P
  rw [matrixTraceReal_projection_rank 1 (matrixProjection_sum P hP horth)] at he
  simp only [matrixTraceReal_projection_rank 1 (hP _), Nat.cast_one, div_one] at he
  exact_mod_cast he

omit [Fintype μ] in
theorem matrixProjection_rank_sub_add {P Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hle : Q ≤ P) :
    (P - Q).rank + Q.rank = P.rank := by
  have hs := (hQ.le_iff_sub hP).mp hle
  have he := matrixTraceReal_sub 1 P Q
  simp only [matrixTraceReal_projection_rank 1 hs, matrixTraceReal_projection_rank 1 hP,
    matrixTraceReal_projection_rank 1 hQ, Nat.cast_one, div_one] at he
  have hf : ((P - Q).rank : ℝ) + (Q.rank : ℝ) = (P.rank : ℝ) := by linarith
  exact_mod_cast hf

omit [Fintype μ] in
theorem matrixProjection_rank_one_sub_add {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    (1 - P).rank + P.rank = Fintype.card ι := by
  have he := matrixProjection_rank_sub_add (IsStarProjection.one (R := Matrix ι ι ℂ)) hP hP.le_one
  simpa only [Matrix.rank_one] using he

omit [Fintype μ] in
theorem matrixProjection_subprojections_orthogonal {P Q E F : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hE : IsStarProjection E) (hF : IsStarProjection F)
    (hPE : P ≤ E) (hQF : Q ≤ F) (hEF : E * F = 0) : P * Q = 0 := by
  have hp := (hP.le_iff_mul_eq_left hE).mp hPE
  have hq := (hQ.le_iff_mul_eq_right hF).mp hQF
  calc
    P * Q = (P * E) * (F * Q) := by rw [hp, hq]
    _ = P * (E * F) * Q := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hEF, Matrix.mul_zero, Matrix.zero_mul]

end ThomGame.Analysis
