module

public import ThomGame.Analysis.MatrixProjectionRankSums

/-!
# A prescribed intermediate rank between nested projections

Remove a suitable subprojection from the orthogonal difference. This
keeps the smaller projection and stays inside the larger one.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_matrixProjection_intermediate_rank {P Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P ≤ Q)
    (n : Nat) (hPn : P.rank ≤ n) (hnQ : n ≤ Q.rank) :
    ∃ R : Matrix ι ι ℂ, IsStarProjection R ∧ P ≤ R ∧ R ≤ Q ∧ R.rank = n := by
  have hQP : IsStarProjection (Q - P) := (hP.le_iff_sub hQ).mp hPQ
  have hdiff := matrixProjection_rank_sub_add hQ hP hPQ
  have hsmall : Q.rank - n ≤ (Q - P).rank := by omega
  obtain ⟨S, hS, hSQP, hrank⟩ := exists_matrixSubprojection_rank hQP (Q.rank - n) hsmall
  have hSQ : S ≤ Q := hSQP.trans (sub_le_self Q hP.nonneg)
  refine ⟨Q - S, (hS.le_iff_sub hQ).mp hSQ, ?_, sub_le_self Q hS.nonneg, ?_⟩
  · simpa only [le_sub_iff_add_le, add_comm] using hSQP
  · have hr := matrixProjection_rank_sub_add hQ hS hSQ
    omega

theorem matrixProjection_eq_of_le_rank_eq {P Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P ≤ Q) (hr : P.rank = Q.rank) : P = Q := by
  have hdiff := matrixProjection_rank_sub_add hQ hP hPQ
  have hz : (Q - P).rank = 0 := by omega
  have hproj : IsStarProjection (Q - P) := (hP.le_iff_sub hQ).mp hPQ
  have ht : matrixTraceReal 1 (Q - P) = 0 := by
    rw [matrixTraceReal_projection_rank 1 hproj, hz, Nat.cast_zero, zero_div]
  have hn : rectHSNorm 1 (Q - P) ^ 2 = 0 := by
    rw [← matrixTraceReal_gram, hproj.isSelfAdjoint.isHermitian.eq, hproj.isIdempotentElem.eq, ht]
  have he : Q - P = 0 := (rectHSNorm_eq_zero_iff (by norm_num : 0 < (1 : Nat)) _).mp
    (sq_eq_zero_iff.mp hn)
  exact (sub_eq_zero.mp he).symm

end ThomGame.Analysis
