module

public import ThomGame.Analysis.MatrixBlockSubrank

/-!
# Correcting the rounded block projection to the original rank

A nested rank correction costs at most the absolute trace change
in squared distance to any projection. Combining it with the half
cut gives the rank-preserving bound four times the pinching defect.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [Fintype μ] in
theorem rectHSNorm_projection_nested_correction (r : Nat) {P Q R : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (hnest : R ≤ Q ∨ Q ≤ R) :
    rectHSNorm r (P - R) ^ 2 ≤ rectHSNorm r (P - Q) ^ 2 +
      |matrixTraceReal r R - matrixTraceReal r Q| := by
  rw [rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian hR.isSelfAdjoint.isHermitian,
    rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian hQ.isSelfAdjoint.isHermitian,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hR.isIdempotentElem.eq]
  rcases hnest with hle | hle
  · have hd := (hR.le_iff_sub hQ).mp hle
    have he := matrixTraceReal_projection_product_le r hd hP
    rw [matrixTraceReal_mul_comm r (Q - R) P, Matrix.mul_sub, matrixTraceReal_sub,
      matrixTraceReal_sub] at he
    rw [abs_of_nonpos (sub_nonpos.mpr (matrixTraceReal_mono r hle))]
    linarith
  · have hd := (hQ.le_iff_sub hR).mp hle
    have he := matrixTraceReal_projection_product_nonneg r hd hP
    rw [matrixTraceReal_mul_comm r (R - Q) P, Matrix.mul_sub, matrixTraceReal_sub] at he
    rw [abs_of_nonneg (sub_nonneg.mpr (matrixTraceReal_mono r hle))]
    linarith

theorem exists_matrixPinching_rank_corrected (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    ∃ R : Matrix ι ι ℂ, IsStarProjection R ∧ R.rank = P.rank ∧
      (∀ i, Commute (E i) R) ∧
      rectHSNorm r (P - R) ^ 2 ≤ 4 * rectHSNorm r (P - matrixBlockPinch E P) ^ 2 := by
  let Q := matrixHalfProjection (matrixBlockPinch E P)
  have hQ : IsStarProjection Q := matrixHalfProjection_isStarProjection _
  obtain ⟨R, hR, hrank, hnest, hcomm⟩ := exists_matrixBlockProjection_rank E hE horth hsum hQ
    (matrixHalfProjection_pinching_commute E hE horth hP) P.rank P.rank_le_card_width
  refine ⟨R, hR, hrank, hcomm, ?_⟩
  have hn := rectHSNorm_projection_nested_correction r hP hQ hR hnest
  have htrace : matrixTraceReal r R = matrixTraceReal r P := by
    rw [matrixTraceReal_projection_rank r hR, matrixTraceReal_projection_rank r hP, hrank]
  rw [htrace, abs_sub_comm] at hn
  have hd := matrixHalfProjection_pinching_distance_le r E hE horth hsum hP
  have ht := matrixHalfProjection_pinching_trace_error_le r E hE horth hsum hP
  change rectHSNorm r (P - Q) ^ 2 ≤ _ at hd
  change |matrixTraceReal r Q - matrixTraceReal r P| ≤ _ at ht
  linarith

end ThomGame.Analysis
