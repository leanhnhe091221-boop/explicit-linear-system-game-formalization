module

public import ThomGame.Analysis.MatrixInclusionMultiplicity
public import ThomGame.Analysis.MatrixStarBlockSupports

/-!
# Actual joint central cells of an inclusion

Their ranks are p_i s_j k_ji. In particular, the cells that occur are
exactly those with positive Bratteli multiplicity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

noncomputable def matrixInclusionCell (j : Fin Q.count) (i : Fin P.count) : CMatrix d :=
  matrixStarBlockSupport C Q j * matrixStarBlockSupport B P i

include hBC in
theorem matrixInclusion_supports_commute (j : Fin Q.count) (i : Fin P.count) :
    Commute (matrixStarBlockSupport C Q j) (matrixStarBlockSupport B P i) :=
  matrixStarBlockSupport_commutes C Q j _ (hBC (matrixStarBlockSupport_mem B P i))

include hBC in
theorem matrixInclusionCell_projection (j : Fin Q.count) (i : Fin P.count) :
    IsStarProjection (matrixInclusionCell B C P Q j i) :=
  (matrixStarBlockSupport_projection C Q j).mul (matrixStarBlockSupport_projection B P i)
    (matrixInclusion_supports_commute B C P Q hBC j i)

theorem matrixInclusionCell_sum : ∑ j, ∑ i, matrixInclusionCell B C P Q j i = 1 := by
  simp only [matrixInclusionCell, ← Finset.mul_sum, matrixStarBlockSupport_sum B P, Matrix.mul_one,
    matrixStarBlockSupport_sum C Q]

theorem matrixInclusionCell_rank (j : Fin Q.count) (i : Fin P.count) :
    (matrixInclusionCell B C P Q j i).rank =
      P.size i * matrixStarRepresentationMultiplicity C Q C.subtype j * matrixInclusionMultiplicity B C P Q hBC j i := by
  let X : C := StarSubalgebra.inclusion hBC (matrixAlgebraicBlockSupport B P.toAlgebraic i)
  have hX : IsIdempotentElem X := by
    change X * X = X
    dsimp only [X]
    rw [← map_mul, matrixAlgebraicBlockSupport_mul_self]
  have he := matrixAlgebraicRepresentation_block_cut_rank C Q.toAlgebraic C.subtype.toAlgHom X hX j
  have hr := matrixAlgebraicRepresentation_support_rank B P.toAlgebraic
    (matrixInclusionBlockRepresentation B C Q hBC j).toAlgHom i
  change (Q.equiv X j).rank = P.size i * matrixInclusionMultiplicity B C P Q hBC j i at hr
  change (matrixInclusionCell B C P Q j i).rank =
    matrixStarRepresentationMultiplicity C Q C.subtype j * (Q.equiv X j).rank at he
  rw [hr] at he
  exact he.trans (by ac_rfl)

theorem matrixInclusionCell_zero_iff (j : Fin Q.count) (i : Fin P.count) :
    matrixInclusionCell B C P Q j i = 0 ↔ matrixInclusionMultiplicity B C P Q hBC j i = 0 := by
  have hp := P.size_pos i
  have hs := matrixStarRepresentationMultiplicity_pos C Q C.subtype Subtype.val_injective j
  constructor
  · intro hz
    have he := matrixInclusionCell_rank B C P Q hBC j i
    rw [hz, Matrix.rank_zero] at he
    exact (Nat.mul_eq_zero.mp he.symm).resolve_left (Nat.ne_of_gt (Nat.mul_pos hp hs))
  · intro hk
    by_contra hne
    have hpos := matrixIdempotent_rank_pos
      (matrixInclusionCell_projection B C P Q hBC j i).isIdempotentElem hne
    rw [matrixInclusionCell_rank B C P Q hBC, hk, Nat.mul_zero] at hpos
    omega

theorem matrixInclusionCell_trace (r : Nat) (j : Fin Q.count) (i : Fin P.count) :
    matrixTraceReal r (matrixInclusionCell B C P Q j i) =
      ((P.size i : ℝ) * matrixStarRepresentationMultiplicity C Q C.subtype j *
        matrixInclusionMultiplicity B C P Q hBC j i) / r := by
  rw [matrixTraceReal_projection_rank r (matrixInclusionCell_projection B C P Q hBC j i),
    matrixInclusionCell_rank B C P Q hBC]
  simp only [Nat.cast_mul]

end ThomGame.Analysis
