module

public import ThomGame.Analysis.MatrixCornerComplementAlgebra

/-!
# Actual supported corners of finite matrix star subalgebras

The corner is a nonunital star subalgebra. When p belongs to A, its
carrier is exactly the set of actual compressions p X p for X in A.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

def matrixSubalgebraCorner (A : StarSubalgebra ℂ (CMatrix d)) (p : CMatrix d)
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ (CMatrix d) :=
  A.toNonUnitalStarSubalgebra ⊓ matrixCornerNonUnitalAlgebra p hp

theorem mem_matrixSubalgebraCorner (A : StarSubalgebra ℂ (CMatrix d)) (p : CMatrix d)
    (hp : IsStarProjection p) (X : CMatrix d) :
    X ∈ matrixSubalgebraCorner A p hp ↔ X ∈ A ∧ p * X = X ∧ X * p = X := Iff.rfl

theorem matrixSubalgebraCorner_compression_mem (A : StarSubalgebra ℂ (CMatrix d))
    {p : CMatrix d} (hp : IsStarProjection p) (hpA : p ∈ A) (X : CMatrix d) (hX : X ∈ A) :
    p * X * p ∈ matrixSubalgebraCorner A p hp := by
  refine ⟨A.mul_mem (A.mul_mem hpA hX) hpA, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq]
  · rw [mul_assoc, hp.isIdempotentElem.eq]

theorem matrixSubalgebraCorner_compression_eq (A : StarSubalgebra ℂ (CMatrix d))
    {p : CMatrix d} (hp : IsStarProjection p) (X : CMatrix d)
    (hX : X ∈ matrixSubalgebraCorner A p hp) : p * X * p = X := by
  rw [hX.2.1, hX.2.2]

theorem matrixSubalgebraCorner_eq_compressions (A : StarSubalgebra ℂ (CMatrix d))
    {p : CMatrix d} (hp : IsStarProjection p) (hpA : p ∈ A) :
    (matrixSubalgebraCorner A p hp : Set (CMatrix d)) =
      (fun X : CMatrix d => p * X * p) '' (A : Set (CMatrix d)) := by
  ext X
  constructor
  · intro hX
    exact ⟨X, hX.1, matrixSubalgebraCorner_compression_eq A hp X hX⟩
  · rintro ⟨Y, hY, rfl⟩
    exact matrixSubalgebraCorner_compression_mem A hp hpA Y hY

end ThomGame.Analysis
