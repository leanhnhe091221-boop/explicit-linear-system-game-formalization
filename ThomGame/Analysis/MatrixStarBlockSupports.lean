module

public import ThomGame.Analysis.MatrixStarBlockUnits
public import ThomGame.Analysis.MatrixProjectionSubrank

/-!
# Actual central projection partitions for star blocks
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)

noncomputable abbrev matrixStarBlockSupport (i : Fin P.count) : CMatrix d :=
  (matrixAlgebraicBlockSupport A P.toAlgebraic i : CMatrix d)

theorem matrixStarBlockSupport_projection (i : Fin P.count) : IsStarProjection (matrixStarBlockSupport A P i) :=
  matrixAlgebraicBlockSupport_projection A P.toAlgebraic i

theorem matrixStarBlockSupport_mem (i : Fin P.count) : matrixStarBlockSupport A P i ∈ A :=
  (matrixAlgebraicBlockSupport A P.toAlgebraic i).property

theorem matrixStarBlockSupport_commutes (i : Fin P.count) (X : CMatrix d) (hX : X ∈ A) :
    Commute (matrixStarBlockSupport A P i) X :=
  congrArg Subtype.val (matrixAlgebraicBlockSupport_commutes A P.toAlgebraic i ⟨X, hX⟩)

theorem matrixStarBlockSupport_orthogonal :
    Pairwise (fun i j => matrixStarBlockSupport A P i * matrixStarBlockSupport A P j = 0) := by
  intro i j hij
  exact congrArg Subtype.val (matrixAlgebraicBlockSupport_mul_of_ne A P.toAlgebraic i j hij)

theorem matrixStarBlockSupport_sum : ∑ i, matrixStarBlockSupport A P i = 1 := by
  change (∑ i, A.subtype (matrixAlgebraicBlockSupport A P.toAlgebraic i)) = 1
  rw [← map_sum, matrixAlgebraicBlockSupport_sum, map_one]

theorem matrixStarBlockSupport_rank (i : Fin P.count) :
    (matrixStarBlockSupport A P i).rank = P.size i * matrixStarRepresentationMultiplicity A P A.subtype i :=
  matrixAlgebraicRepresentation_support_rank A P.toAlgebraic A.subtype.toAlgHom i

theorem matrixStarBlockSupport_trace (r : Nat) (i : Fin P.count) :
    matrixTraceReal r (matrixStarBlockSupport A P i) =
      ((P.size i : ℝ) * matrixStarRepresentationMultiplicity A P A.subtype i) / r := by
  rw [matrixTraceReal_projection_rank r (matrixStarBlockSupport_projection A P i),
    matrixStarBlockSupport_rank A P i, Nat.cast_mul]

end ThomGame.Analysis
