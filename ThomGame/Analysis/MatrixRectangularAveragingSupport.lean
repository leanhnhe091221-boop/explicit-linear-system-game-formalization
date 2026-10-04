module

public import ThomGame.Analysis.MatrixRectangularAveraging

/-!
# Closed convex averaging preserves actual range support
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {d m : Nat}

theorem matrix_closedConvexHull_preserves_range (Q : CMatrix m)
    (O : Set (Matrix (Fin m) (Fin d) ℂ)) (hO : ∀ X ∈ O, Q * X = X)
    (Y : Matrix (Fin m) (Fin d) ℂ) (hY : Y ∈ closedConvexHull ℝ O) : Q * Y = Y := by
  let C : Matrix (Fin m) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin d) ℂ :=
    { toFun := fun X => Q * X - X
      map_add' := fun X Z => by rw [Matrix.mul_add]; abel
      map_smul' := fun c X => by rw [Matrix.mul_smul, smul_sub]; rfl }
  let K := (C.restrictScalars ℝ).toContinuousLinearMap
  have hsub : closedConvexHull ℝ O ⊆ K ⁻¹' {0} := by
    apply closedConvexHull_min
    · intro X hX
      exact sub_eq_zero.mpr (hO X hX)
    · exact (convex_singleton (0 : Matrix (Fin m) (Fin d) ℂ)).linear_preimage K.toLinearMap
    · exact isClosed_singleton.preimage K.continuous
  exact sub_eq_zero.mp (hsub hY)

theorem matrixRectangularUnitaryAction_preserves_range {B : StarSubalgebra ℂ (CMatrix d)}
    (ρ : B →⋆ₐ[ℂ] CMatrix m) (Q : CMatrix m) (X : Matrix (Fin m) (Fin d) ℂ)
    (hX : Q * X = X) (hQ : ∀ b : B, Q * ρ b = ρ b * Q) (U : unitary B) :
    Q * matrixRectangularUnitaryAction ρ U X = matrixRectangularUnitaryAction ρ U X := by
  rw [matrixRectangularUnitaryAction_apply, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q,
    hQ, Matrix.mul_assoc (ρ U.val) Q X, hX]

end ThomGame.Analysis
