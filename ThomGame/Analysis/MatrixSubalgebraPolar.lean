module

public import ThomGame.Analysis.MatrixUnitaryCorrection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Polar correction of invertible matrices inside their original subalgebra

Functional calculus preserves the actual finite-dimensional star
subalgebra. For an invertible matrix its polar factor is already unitary,
so no arbitrary choice of a complementary partial isometry is needed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixRectAbs_mem_subalgebra (A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ A) : matrixRectAbs X ∈ A := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  rw [matrixRectAbs, matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self X).nonneg]
  exact cfc_mem (𝕜' := ℂ) (s := A) Real.sqrt (A.mul_mem (A.star_mem' hX) hX)

theorem matrixRectPolar_mem_subalgebra (A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ A) : matrixRectPolar X ∈ A := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact A.mul_mem hX (cfc_mem (𝕜' := ℂ) (s := A) (fun t : ℝ => t⁻¹) (matrixRectAbs_mem_subalgebra A hX))

theorem matrixRectPolar_mem_unitary_of_isUnit {X : CMatrix d} (hX : IsUnit X) :
    matrixRectPolar X ∈ unitary (CMatrix d) := by
  have hs : matrixRealSupport (matrixRectAbs X) = 1 :=
    hX.mul_left_cancel (by rw [matrix_mul_absSupport, mul_one])
  have hi : (matrixRectPolar X)ᴴ * matrixRectPolar X = 1 := by rw [matrixRectPolar_initial, hs]
  exact ⟨hi, mul_eq_one_comm.mp hi⟩

theorem exists_matrixSubalgebraUnitary_close_of_isUnit [NeZero d]
    (A : StarSubalgebra ℂ (CMatrix d)) {X : CMatrix d} (hX : X ∈ A) (hi : IsUnit X) :
    ∃ U : UnitaryMatrix d, U.val ∈ A ∧ hsNorm (X - U.val) ≤ hsNorm (Xᴴ * X - 1) := by
  let U : UnitaryMatrix d := ⟨matrixRectPolar X, matrixRectPolar_mem_unitary_of_isUnit hi⟩
  refine ⟨U, matrixRectPolar_mem_subalgebra A hX, ?_⟩
  calc
    hsNorm (X - U.val) = hsNorm (U.val * (matrixRectAbs X - 1)) := by
      congr 1
      rw [mul_sub, mul_one]
      exact congrArg (fun Y => Y - U.val) (matrixRectPolar_mul_abs X).symm
    _ = hsNorm (matrixRectAbs X - 1) := hsNorm_unitary_mul U _
    _ ≤ hsNorm (Xᴴ * X - 1) := matrixRectAbs_sub_one_le_gram X

end ThomGame.Analysis
