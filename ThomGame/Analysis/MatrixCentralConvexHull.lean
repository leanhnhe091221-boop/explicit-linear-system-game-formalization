module

public import ThomGame.Analysis.HilbertInvariantConvexHull
public import ThomGame.Analysis.MatrixSubalgebraUnitaries
public import ThomGame.Analysis.MatrixTraceProjection
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A central matrix near a uniformly almost conjugation-invariant matrix

The least-norm point in the closed convex hull of the unitary orbit lies
in the actual center. All estimates use the ambient normalized trace norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem exists_matrixCentral_near_of_commutator_bound (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (hX : X ∈ A) (C : ℝ)
    (hbound : ∀ U : unitary A,
      hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) ≤ C) :
    ∃ Y ∈ starSubalgebraCenter A, hsNorm (X - Y) ≤ C := by
  let : InnerProductSpace ℝ (FiniteMatrixHilbert d) := InnerProductSpace.rclikeToReal ℂ _
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ (FiniteMatrixHilbert d)
  let T (U : unitary A) : FiniteMatrixHilbert d →L[ℝ] FiniteMatrixHilbert d :=
    (matrixConjugationHilbert (matrixSubalgebraUnitary A U)).toContinuousLinearMap.restrictScalars ℝ
  let S := Set.range (fun U : unitary A => T U (finiteMatrixHilbertEquiv d X))
  have hinv (U : unitary A) : Set.MapsTo (T U) S S := by
    rintro z ⟨V, rfl⟩
    refine ⟨U * V, ?_⟩
    change finiteMatrixHilbertEquiv d (matrixUnitaryConjugation (matrixSubalgebraUnitary A (U * V)) X) =
      finiteMatrixHilbertEquiv d (matrixUnitaryConjugation (matrixSubalgebraUnitary A U)
        (matrixUnitaryConjugation (matrixSubalgebraUnitary A V) X))
    simp only [matrixSubalgebraUnitary_mul, matrixUnitaryConjugation_apply,
      Matrix.UnitaryGroup.mul_val, star_mul, mul_assoc]
  have hnorm (U : unitary A) (z : FiniteMatrixHilbert d) : ‖T U z‖ = ‖z‖ :=
    (matrixConjugationHilbert (matrixSubalgebraUnitary A U)).norm_map z
  have hb : ∀ z ∈ S, ‖z - finiteMatrixHilbertEquiv d X‖ ≤ C := by
    rintro z ⟨U, rfl⟩
    exact (matrixConjugationHilbert_sub_norm (matrixSubalgebraUnitary A U) X).trans_le (hbound U)
  obtain ⟨y, hy, hfix, hdist⟩ := exists_fixed_near_of_invariant_set T S
    ⟨T 1 (finiteMatrixHilbertEquiv d X), ⟨1, rfl⟩⟩ hinv hnorm (finiteMatrixHilbertEquiv d X) C hb
  have hsub : closedConvexHull ℝ S ⊆ (matrixTraceSubmodule A : Set (FiniteMatrixHilbert d)) := by
    apply closedConvexHull_min
    · rintro z ⟨U, rfl⟩
      change (matrixSubalgebraUnitary A U).val * X * star (matrixSubalgebraUnitary A U).val ∈ A
      exact A.mul_mem (A.mul_mem U.val.property hX) (A.star_mem' U.val.property)
    · exact ((matrixTraceSubmodule A).restrictScalars ℝ).convex
    · exact (matrixTraceSubmodule A).closed_of_finiteDimensional
  let Y := (finiteMatrixHilbertEquiv d).symm y
  have hY : Y ∈ A := hsub hy
  refine ⟨Y, matrixSubalgebraCenter_mem_of_unitaries A Y hY ?_, ?_⟩
  · intro U
    have he := congrArg (finiteMatrixHilbertEquiv d).symm (hfix U)
    change (matrixSubalgebraUnitary A U).val * Y * star (matrixSubalgebraUnitary A U).val = Y at he
    have hm := congrArg (fun Z => Z * (matrixSubalgebraUnitary A U).val) he
    simpa only [mul_assoc, (matrixSubalgebraUnitary A U).prop.1, mul_one] using hm
  · rw [hsNorm_sub_comm, ← finiteMatrixHilbert_norm, map_sub]
    change ‖finiteMatrixHilbertEquiv d ((finiteMatrixHilbertEquiv d).symm y) - finiteMatrixHilbertEquiv d X‖ ≤ C
    rwa [(finiteMatrixHilbertEquiv d).apply_symm_apply]

end ThomGame.Analysis
