module

public import ThomGame.Analysis.MatrixExpectationCompletelyPositive
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Choi square roots with coefficients in the actual range subalgebra

Keeping the Choi blocks in A is what permits an exact action of A's
commutant on the Stinespring space.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixSubalgebra_choi_factor (A : StarSubalgebra ℂ (CMatrix d))
    (F : CMatrix d →CP CMatrix d) (hF : ∀ X, F X ∈ A) :
    ∃ S : CStarMatrix (Fin d) (Fin d) (CMatrix d),
      (∀ i j, S i j ∈ A) ∧
      ∀ X, F X = ∑ k, star (matrixChoiKraus S k) * X * matrixChoiKraus S k := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin d) (Fin d) (CMatrix d)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin d) (Fin d) (CMatrix d)) :=
    CStarAlgebra.instNonnegSpectrumClass
  let C : CStarMatrix (Fin d) (Fin d) (CMatrix d) :=
    (CStarMatrix.ofMatrix (fun i j => Matrix.single i j (1 : ℂ))).map F
  have hC : 0 ≤ C := F.map_cstarMatrix_nonneg _ matrixChoi_input_nonneg
  let B : StarSubalgebra ℂ (CStarMatrix (Fin d) (Fin d) (CMatrix d)) := matrixBlockSubalgebra A
  let : FiniteDimensional ℂ (CStarMatrix (Fin d) (Fin d) (CMatrix d)) :=
    Module.Finite.equiv CStarMatrix.ofMatrixₗ
  let : IsClosed (B : Set (CStarMatrix (Fin d) (Fin d) (CMatrix d))) :=
    B.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  have hCB : C ∈ B := fun i j => hF (Matrix.single i j 1)
  have hS : CFC.sqrt C ∈ B := by
    rw [CFC.sqrt_eq_real_sqrt C hC]
    exact cfcₙ_mem (𝕜' := ℂ) (s := B) Real.sqrt hCB
  refine ⟨CFC.sqrt C, hS, matrixKraus_of_choi_factor F _ ?_⟩
  rw [(CFC.sqrt_nonneg C).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self C hC]

end ThomGame.Analysis
