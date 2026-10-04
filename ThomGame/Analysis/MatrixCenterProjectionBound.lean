module

public import ThomGame.Analysis.MatrixCentralConvexHull
public import ThomGame.Analysis.MatrixConditionalExpectation

/-!
# Central trace projection is controlled by unitary commutators

A single actual unitary witnesses at least half the distance to the center.
This dimension-independent estimate supplies bounded coordinate witnesses.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem matrixTraceProjection_bestApproximation (A : StarSubalgebra ℂ (CMatrix d))
    (X Y : CMatrix d) (hY : Y ∈ A) :
    hsNorm (X - matrixTraceProjection A X) ≤ hsNorm (X - Y) := by
  have h : ‖finiteMatrixHilbertEquiv d X - (matrixTraceSubmodule A).starProjection (finiteMatrixHilbertEquiv d X)‖ ≤
      ‖finiteMatrixHilbertEquiv d X - finiteMatrixHilbertEquiv d Y‖ := by
    have hbelow : BddBelow (Set.range (fun Z : matrixTraceSubmodule A =>
        ‖finiteMatrixHilbertEquiv d X - Z.val‖)) := ⟨0, by
      rintro t ⟨Z, rfl⟩
      exact norm_nonneg _⟩
    have hi := ciInf_le hbelow (⟨finiteMatrixHilbertEquiv d Y, hY⟩ : matrixTraceSubmodule A)
    exact (Submodule.starProjection_minimal (U := matrixTraceSubmodule A)
      (finiteMatrixHilbertEquiv d X)).le.trans hi
  simpa only [← matrixTraceProjection_embedding, ← map_sub, finiteMatrixHilbert_norm] using h

theorem matrixCenterProjection_error_le (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (hX : X ∈ A) (C : ℝ)
    (hbound : ∀ U : unitary A,
      hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) ≤ C) :
    hsNorm (X - matrixTraceProjection (starSubalgebraCenter A) X) ≤ C := by
  obtain ⟨Y, hY, hdist⟩ := exists_matrixCentral_near_of_commutator_bound A X hX C hbound
  exact (matrixTraceProjection_bestApproximation (starSubalgebraCenter A) X Y hY).trans hdist

theorem exists_matrixUnitary_detecting_center_distance (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (hX : X ∈ A) :
    ∃ U : unitary A, hsNorm (X - matrixTraceProjection (starSubalgebraCenter A) X) ≤
      2 * hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) := by
  let r := hsNorm (X - matrixTraceProjection (starSubalgebraCenter A) X)
  by_cases hz : r = 0
  · refine ⟨1, ?_⟩
    change r ≤ _
    rw [hz]
    exact mul_nonneg (by norm_num) (hsNorm_nonneg _)
  · by_contra h
    have hb : ∀ U : unitary A,
        hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) ≤ r / 2 := by
      intro U
      have hu : 2 * hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) < r :=
        lt_of_not_ge (fun hh => h ⟨U, hh⟩)
      linarith
    have he := matrixCenterProjection_error_le A X hX (r / 2) hb
    change r ≤ r / 2 at he
    have hr : 0 < r := lt_of_le_of_ne (hsNorm_nonneg _) (Ne.symm hz)
    linarith

end ThomGame.Analysis
