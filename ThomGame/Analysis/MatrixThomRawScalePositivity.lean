module

public import ThomGame.Analysis.MatrixThomRetainedScales

/-!
# Positivity of the original-parameter scales on the corrected space
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem MatrixThomSpectralData.rawSourceScale_posDef (P : MatrixSubalgebraStarBlocks B) :
    (S.rawSourceScale P).PosDef := by
  change (S.cutSourceRepresentation (matrixStarBlockScalarElement B P _)).PosDef
  rw [← matrixStarRepresentationRetainedBlocks_scalar]
  exact matrixStarBlockScalar_posDef _ _ (fun i => matrixSubalgebraScale_coefficient_pos B P _)

theorem MatrixThomSpectralData.rawTargetScale_posDef
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))) :
    (S.rawTargetScale R).PosDef := by
  change (S.cutCommutantRepresentation (matrixStarBlockScalarElement _ R _)).PosDef
  rw [← matrixStarRepresentationRetainedComplementary_scalar]
  apply matrixStarBlockScalar_posDef
  intro i
  exact div_pos (Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos _ R _ Subtype.val_injective _))
    (Nat.cast_pos.mpr (R.size_pos _))

end ThomGame.Analysis
