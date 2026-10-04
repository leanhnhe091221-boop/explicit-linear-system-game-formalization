module

public import ThomGame.Analysis.MatrixCenterProjectionBound

/-!
# Distance to a matrix subalgebra's commutant

Unitary conjugation averaging, implemented by the least-norm point in a
closed convex hull, applies to every ambient matrix. A single unitary
of the subalgebra detects at least half the distance to its commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat}

theorem mem_matrixSubalgebraCommutant_iff (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) ↔ ∀ Y ∈ A, Y * X = X * Y := by
  rw [StarSubalgebra.mem_centralizer_iff]
  exact ⟨fun h Y hY => (h Y hY).1, fun h Y hY => ⟨h Y hY, h (star Y) (A.star_mem' hY)⟩⟩

variable [NeZero d]

theorem exists_matrixCommutant_near_of_commutator_bound (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (C : ℝ)
    (hbound : ∀ U : unitary A,
      hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) ≤ C) :
    ∃ Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)), hsNorm (X - Y) ≤ C := by
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
  obtain ⟨y, _, hfix, hdist⟩ := exists_fixed_near_of_invariant_set T S
    ⟨T 1 (finiteMatrixHilbertEquiv d X), ⟨1, rfl⟩⟩ hinv hnorm (finiteMatrixHilbertEquiv d X) C hb
  let Y := (finiteMatrixHilbertEquiv d).symm y
  refine ⟨Y, (mem_matrixSubalgebraCommutant_iff A Y).mpr ?_, ?_⟩
  · apply matrixSubalgebra_commute_of_unitaries A Y
    intro U
    have he := congrArg (finiteMatrixHilbertEquiv d).symm (hfix U)
    change (matrixSubalgebraUnitary A U).val * Y * star (matrixSubalgebraUnitary A U).val = Y at he
    have hm := congrArg (fun Z => Z * (matrixSubalgebraUnitary A U).val) he
    simpa only [mul_assoc, (matrixSubalgebraUnitary A U).prop.1, mul_one] using hm
  · rw [hsNorm_sub_comm, ← finiteMatrixHilbert_norm, map_sub]
    change ‖finiteMatrixHilbertEquiv d ((finiteMatrixHilbertEquiv d).symm y) - finiteMatrixHilbertEquiv d X‖ ≤ C
    rwa [(finiteMatrixHilbertEquiv d).apply_symm_apply]

theorem matrixCommutantProjection_error_le (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (C : ℝ)
    (hbound : ∀ U : unitary A,
      hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) ≤ C) :
    hsNorm (X - matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X) ≤ C := by
  obtain ⟨Y, hY, hdist⟩ := exists_matrixCommutant_near_of_commutator_bound A X C hbound
  exact (matrixTraceProjection_bestApproximation _ X Y hY).trans hdist

theorem exists_matrixUnitary_detecting_commutant_distance (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    ∃ U : unitary A, hsNorm (X - matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X) ≤
      2 * hsNorm ((matrixSubalgebraUnitary A U).val * X - X * (matrixSubalgebraUnitary A U).val) := by
  let r := hsNorm (X - matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X)
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
    have he := matrixCommutantProjection_error_le A X (r / 2) hb
    change r ≤ r / 2 at he
    have hr : 0 < r := lt_of_le_of_ne (hsNorm_nonneg _) (Ne.symm hz)
    linarith

end ThomGame.Analysis
