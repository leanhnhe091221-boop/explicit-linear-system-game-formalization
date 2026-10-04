module

public import ThomGame.Analysis.MatrixCommutantConvexHull

/-!
# The actual commutant expectation lies in the closed convex unitary orbit

This identifies the least-norm invariant point with trace expectation.
Consequently every continuous real linear inequality on the unitary
orbit holds for the expectation, with no averaging measure assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

omit [NeZero d] in
theorem matrixSubalgebraConjugation_fixes_commutant
    (A : StarSubalgebra ℂ (CMatrix d)) (U : unitary A) (X : CMatrix d)
    (hX : X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X = X := by
  have hc := (mem_matrixSubalgebraCommutant_iff A X).mp hX
    (matrixSubalgebraUnitary A U).val U.val.property
  rw [matrixUnitaryConjugation_apply, hc, mul_assoc,
    (matrixSubalgebraUnitary A U).prop.2, mul_one]

theorem matrixCommutantProjection_conjugation
    (A : StarSubalgebra ℂ (CMatrix d)) (U : unitary A) (X : CMatrix d) :
    matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))
        (matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X) =
      matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X := by
  let C := StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))
  apply matrixTraceProjection_unique C _ _ (matrixTraceProjection_mem C X)
  intro Z hZ
  rw [mul_sub, normalizedTrace_sub, matrixTraceProjection_pairing C X Z hZ]
  have hp := matrixUnitaryConjugation_pairing (matrixSubalgebraUnitary A U)⁻¹ Z X
  have hf : matrixUnitaryConjugation (matrixSubalgebraUnitary A U)⁻¹ Z = Z :=
    matrixSubalgebraConjugation_fixes_commutant A U⁻¹ Z hZ
  rw [hf, inv_inv] at hp
  exact sub_eq_zero.mpr hp.symm

theorem matrixCommutantProjection_mem_closedConvexHull
    (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X ∈
      closedConvexHull ℝ (Set.range (fun U : unitary A =>
        matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X)) := by
  let : InnerProductSpace ℝ (FiniteMatrixHilbert d) := InnerProductSpace.rclikeToReal ℂ _
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ (FiniteMatrixHilbert d)
  let : FiniteDimensional ℝ (FiniteMatrixHilbert d) := Module.Finite.trans (R := ℝ) ℂ (FiniteMatrixHilbert d)
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
  obtain ⟨y, hy, hfix⟩ := exists_fixed_mem_closedConvexHull T S
    ⟨T 1 (finiteMatrixHilbertEquiv d X), ⟨1, rfl⟩⟩ hinv hnorm
  let Y := (finiteMatrixHilbertEquiv d).symm y
  let C := StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))
  have hYC : Y ∈ C := by
    apply (mem_matrixSubalgebraCommutant_iff A Y).mpr
    apply matrixSubalgebra_commute_of_unitaries A Y
    intro U
    have he := congrArg (finiteMatrixHilbertEquiv d).symm (hfix U)
    change (matrixSubalgebraUnitary A U).val * Y * star (matrixSubalgebraUnitary A U).val = Y at he
    have hm := congrArg (fun Z => Z * (matrixSubalgebraUnitary A U).val) he
    simpa only [mul_assoc, (matrixSubalgebraUnitary A U).prop.1, mul_one] using hm
  let O := Set.range (fun U : unitary A => matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X)
  let H : FiniteMatrixHilbert d →L[ℝ] CMatrix d :=
    ((finiteMatrixHilbertEquiv d).symm.toLinearMap.restrictScalars ℝ).toContinuousLinearMap
  have hsub : closedConvexHull ℝ S ⊆ H ⁻¹' closedConvexHull ℝ O := by
    apply closedConvexHull_min
    · rintro z ⟨U, rfl⟩
      change matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X ∈ closedConvexHull ℝ O
      exact subset_closedConvexHull ⟨U, rfl⟩
    · exact convex_closedConvexHull.linear_preimage H.toLinearMap
    · exact isClosed_closedConvexHull.preimage H.continuous
  have hYO : Y ∈ closedConvexHull ℝ O := hsub hy
  let E : CMatrix d →L[ℝ] CMatrix d :=
    ((matrixTraceProjection C).restrictScalars ℝ).toContinuousLinearMap
  have hconstant : closedConvexHull ℝ O ⊆ E ⁻¹' {E X} := by
    apply closedConvexHull_min
    · rintro Z ⟨U, rfl⟩
      exact matrixCommutantProjection_conjugation A U X
    · exact (convex_singleton (E X)).linear_preimage E.toLinearMap
    · exact isClosed_singleton.preimage E.continuous
  have he : matrixTraceProjection C Y = matrixTraceProjection C X := hconstant hYO
  rw [matrixTraceProjection_eq_self C Y hYC] at he
  exact he ▸ hYO

theorem matrixCommutantProjection_linear_lower_bound
    (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) (f : CMatrix d →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ U : unitary A, c ≤ f (matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X)) :
    c ≤ f (matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) X) := by
  have hsub : closedConvexHull ℝ (Set.range (fun U : unitary A =>
      matrixUnitaryConjugation (matrixSubalgebraUnitary A U) X)) ⊆ f ⁻¹' Set.Ici c := by
    apply closedConvexHull_min
    · rintro Z ⟨U, rfl⟩
      exact hbound U
    · exact (convex_Ici c).linear_preimage f
    · exact isClosed_Ici.preimage f.toContinuousLinearMap.continuous
  exact hsub (matrixCommutantProjection_mem_closedConvexHull A X)

end ThomGame.Analysis
