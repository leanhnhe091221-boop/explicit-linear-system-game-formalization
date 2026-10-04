module

public import ThomGame.Analysis.MatrixKrausFixedPoints
public import ThomGame.Analysis.MatrixExpectationCompletelyPositive
public import ThomGame.Analysis.MatrixCommutantConvexHull

/-!
# The bicommutant theorem for actual finite matrix star subalgebras

The trace expectation has Kraus coefficients in the commutant. Every
matrix in the double commutant is therefore fixed by that expectation.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem exists_matrixTraceProjection_commutant_kraus (A : StarSubalgebra ℂ (CMatrix d)) :
    ∃ a : Fin d × Fin d → CMatrix d,
      (∀ k, a k ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) ∧
      (∀ X, matrixTraceProjection A X = ∑ k, star (a k) * X * a k) ∧
      ∑ k, star (a k) * a k = 1 := by
  obtain ⟨a, ha, hunit⟩ := exists_matrixTraceProjection_kraus A
  refine ⟨a, ?_, ha, hunit⟩
  intro k
  apply (mem_matrixSubalgebraCommutant_iff A (a k)).mpr
  intro X hX
  exact ((matrixKraus_fixed_iff_commute (matrixTraceProjection A) a ha
    (matrixTraceProjection_one A) (matrixTraceProjection_trace A) X).mp
      (matrixTraceProjection_eq_self A X hX) k).symm

theorem matrixSubalgebra_mem_of_bicommutant (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d)
    (hX : X ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) : Set (CMatrix d))) : X ∈ A := by
  obtain ⟨a, ha, hrep, _⟩ := exists_matrixTraceProjection_commutant_kraus A
  have hfix : matrixTraceProjection A X = X :=
    (matrixKraus_fixed_iff_commute (matrixTraceProjection A) a hrep
      (matrixTraceProjection_one A) (matrixTraceProjection_trace A) X).mpr
        (fun k => (mem_matrixSubalgebraCommutant_iff _ X).mp hX (a k) (ha k))
  rw [← hfix]
  exact matrixTraceProjection_mem A X

omit [NeZero d] in
theorem matrixSubalgebra_le_bicommutant (A : StarSubalgebra ℂ (CMatrix d)) :
    A ≤ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) : Set (CMatrix d)) := by
  intro X hX
  apply (mem_matrixSubalgebraCommutant_iff _ X).mpr
  intro Y hY
  exact ((mem_matrixSubalgebraCommutant_iff A Y).mp hY X hX).symm

theorem matrixSubalgebra_bicommutant_eq (A : StarSubalgebra ℂ (CMatrix d)) :
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) : Set (CMatrix d)) = A :=
  le_antisymm (fun X hX => matrixSubalgebra_mem_of_bicommutant A X hX) (matrixSubalgebra_le_bicommutant A)

end ThomGame.Analysis
