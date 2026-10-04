module

public import ThomGame.Analysis.MatrixUnitaryConjugation
public import ThomGame.Analysis.StarSubalgebraCenter
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unitaries of an actual matrix subalgebra and the test for its center
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat}

def matrixSubalgebraUnitary (A : StarSubalgebra ℂ (CMatrix d)) (U : unitary A) : UnitaryMatrix d :=
  ⟨U.val.val, ⟨congrArg Subtype.val U.prop.1, congrArg Subtype.val U.prop.2⟩⟩

@[simp] theorem matrixSubalgebraUnitary_val (A : StarSubalgebra ℂ (CMatrix d)) (U : unitary A) :
    (matrixSubalgebraUnitary A U).val = U.val.val := rfl

@[simp] theorem matrixSubalgebraUnitary_one (A : StarSubalgebra ℂ (CMatrix d)) :
    matrixSubalgebraUnitary A 1 = 1 := rfl

@[simp] theorem matrixSubalgebraUnitary_mul (A : StarSubalgebra ℂ (CMatrix d)) (U V : unitary A) :
    matrixSubalgebraUnitary A (U * V) = matrixSubalgebraUnitary A U * matrixSubalgebraUnitary A V := rfl

theorem matrixSubalgebra_commute_of_unitaries (A : StarSubalgebra ℂ (CMatrix d)) (Y : CMatrix d)
    (hU : ∀ U : unitary A, (matrixSubalgebraUnitary A U).val * Y = Y * (matrixSubalgebraUnitary A U).val)
    (X : CMatrix d) (hX : X ∈ A) : X * Y = Y * X := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  let D : A →ₗ[ℂ] CMatrix d :=
    (LinearMap.mulRight ℂ Y - LinearMap.mulLeft ℂ Y).comp A.subtype.toLinearMap
  have hspan : Submodule.span ℂ (unitary A : Set A) ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    intro B hB
    exact sub_eq_zero.mpr (hU ⟨B, hB⟩)
  have hx : (⟨X, hX⟩ : A) ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]
    trivial
  exact sub_eq_zero.mp (hspan hx)

theorem matrixSubalgebraCenter_mem_of_unitaries (A : StarSubalgebra ℂ (CMatrix d))
    (Y : CMatrix d) (hY : Y ∈ A)
    (hU : ∀ U : unitary A, (matrixSubalgebraUnitary A U).val * Y = Y * (matrixSubalgebraUnitary A U).val) :
    Y ∈ starSubalgebraCenter A :=
  (mem_starSubalgebraCenter_iff A Y).mpr ⟨hY, matrixSubalgebra_commute_of_unitaries A Y hU⟩

end ThomGame.Analysis
