module

public import ThomGame.Analysis.MatrixStarRepresentationCommutant
public import ThomGame.Analysis.MatrixBicommutant

/-!
# The actual original algebra as standard or complementary blocks

The finite bicommutant theorem identifies the original algebra with
the complementary blocks of a star decomposition of its commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))

theorem matrixSubalgebra_subtype_range : A.subtype.range = A := by
  ext X
  exact ⟨fun ⟨Y, hY⟩ => hY ▸ Y.property, fun hX => ⟨⟨X, hX⟩, rfl⟩⟩

theorem matrixSubalgebra_eq_standard_blocks (P : MatrixSubalgebraStarBlocks A) :
    A = (matrixStarRepresentationBlocks A P A.subtype).range := by
  rw [← matrixStarRepresentation_range_eq_blocks, matrixSubalgebra_subtype_range]

theorem matrixSubalgebra_eq_complementary_blocks [NeZero d]
    (P : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))) :
    A = (matrixStarRepresentationComplementary _ P
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype).range := by
  rw [← matrixStarRepresentation_commutant_eq, matrixSubalgebra_subtype_range,
    matrixSubalgebra_bicommutant_eq]

end ThomGame.Analysis
