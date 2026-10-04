module

public import ThomGame.Analysis.MatrixInclusionCellOrder
public import ThomGame.Analysis.ScalarBoundedScale

/-!
# Bounded scale operators on the actual joint cells

This is the matrix rational function T (T+S)⁻¹, with explicit
positive cell coordinates and exact order properties.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def matrixBoundedScale {d : Nat} (T S : CMatrix d) : CMatrix d := T * (T + S)⁻¹

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixBoundedScale_cellFormula (a s : Fin Q.count → Fin P.count → ℝ)
    (ha : ∀ j i, 0 < a j i) (hs : ∀ j i, 0 < s j i) :
    matrixBoundedScale (matrixInclusionCellScalar B C P Q a) (matrixInclusionCellScalar B C P Q s) =
      matrixInclusionCellScalar B C P Q (fun j i => boundedScaleScalar (a j i) (s j i)) := by
  have hadd : ∀ j i, (a + s) j i ≠ 0 := fun j i => ne_of_gt (add_pos (ha j i) (hs j i))
  rw [matrixBoundedScale, matrixInclusionCellScalar_add,
    matrixInclusionCellScalar_inverse B C P Q hBC (a + s) hadd,
    matrixInclusionCellScalar_mul B C P Q hBC]
  congr 1

include hBC in
theorem matrixBoundedScale_inclusionFormula (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) :
    matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s) =
      matrixInclusionCellScalar B C P Q (fun j i => boundedScaleScalar (a j) (s i)) := by
  rw [← matrixInclusionCellScalar_target B C P Q a, ← matrixInclusionCellScalar_source B C P Q s]
  exact matrixBoundedScale_cellFormula B C P Q hBC _ _ (fun j _ => ha j) (fun _ i => hs i)

include hBC in
theorem matrixBoundedScale_inclusion_posDef (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) :
    (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s)).PosDef := by
  rw [matrixBoundedScale_inclusionFormula B C P Q hBC a s ha hs]
  exact matrixInclusionCellScalar_posDef B C P Q hBC (fun j i => boundedScaleScalar_pos (ha j) (hs i).le)

include hBC in
theorem matrixBoundedScale_inclusion_one_sub_posDef (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) :
    (1 - matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s)).PosDef := by
  rw [matrixBoundedScale_inclusionFormula B C P Q hBC a s ha hs,
    ← matrixInclusionCellScalar_one B C P Q, matrixInclusionCellScalar_sub]
  exact matrixInclusionCellScalar_posDef B C P Q hBC
    (fun j i => sub_pos.mpr (boundedScaleScalar_lt_one (ha j) (hs i)))

include hBC in
theorem matrixBoundedScale_inclusion_mem (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) :
    matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s) ∈ C := by
  rw [matrixBoundedScale_inclusionFormula B C P Q hBC a s ha hs]
  exact matrixInclusionCellScalar_mem B C P Q hBC _

include hBC in
theorem matrixBoundedScale_inclusion_commutes (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) (X : CMatrix d) (hX : X ∈ B) :
    Commute (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s)) X := by
  rw [matrixBoundedScale_inclusionFormula B C P Q hBC a s ha hs]
  exact matrixInclusionCellScalar_commutes B C P Q hBC _ X hX

end ThomGame.Analysis
