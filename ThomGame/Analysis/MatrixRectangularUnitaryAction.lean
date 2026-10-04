module

public import ThomGame.Analysis.FiniteRectMatrixHilbert
public import ThomGame.Analysis.MatrixSubalgebraUnitaries

/-!
# The unitary action whose fixed matrices are exact intertwiners

The target representation need not be faithful and the two matrix
dimensions may differ. Its action is isometric for every HS normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d m : Nat} {B : StarSubalgebra ℂ (CMatrix d)}

def matrixRepresentationUnitary (ρ : B →⋆ₐ[ℂ] CMatrix m) (U : unitary B) : UnitaryMatrix m :=
  ⟨ρ U.val, Unitary.map_mem ρ U.prop⟩

def matrixRectangularUnitaryAction (ρ : B →⋆ₐ[ℂ] CMatrix m) (U : unitary B) :
    Matrix (Fin m) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin d) ℂ where
  toFun X := ρ U.val * X * (U.val : CMatrix d)ᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem matrixRectangularUnitaryAction_apply (ρ : B →⋆ₐ[ℂ] CMatrix m) (U : unitary B)
    (X : Matrix (Fin m) (Fin d) ℂ) :
    matrixRectangularUnitaryAction ρ U X = ρ U.val * X * (U.val : CMatrix d)ᴴ := rfl

theorem matrixRectangularUnitaryAction_one (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (X : Matrix (Fin m) (Fin d) ℂ) : matrixRectangularUnitaryAction ρ 1 X = X := by
  change ρ 1 * X * (1 : CMatrix d)ᴴ = X
  rw [map_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem matrixRectangularUnitaryAction_mul (ρ : B →⋆ₐ[ℂ] CMatrix m) (U V : unitary B)
    (X : Matrix (Fin m) (Fin d) ℂ) :
    matrixRectangularUnitaryAction ρ (U * V) X =
      matrixRectangularUnitaryAction ρ U (matrixRectangularUnitaryAction ρ V X) := by
  change ρ (U.val * V.val) * X * ((U.val : CMatrix d) * (V.val : CMatrix d))ᴴ = _
  simp only [map_mul, Matrix.conjTranspose_mul, matrixRectangularUnitaryAction_apply, Matrix.mul_assoc]

theorem matrixRectangularUnitaryAction_hsNorm (r : Nat) (ρ : B →⋆ₐ[ℂ] CMatrix m) (U : unitary B)
    (X : Matrix (Fin m) (Fin d) ℂ) :
    rectHSNorm r (matrixRectangularUnitaryAction ρ U X) = rectHSNorm r X :=
  rectHSNorm_two_unitaries r (matrixRepresentationUnitary ρ U) (matrixSubalgebraUnitary B U)⁻¹ X

theorem matrixRectangularUnitaryAction_defect_norm (r : Nat) (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (U : unitary B) (X : Matrix (Fin m) (Fin d) ℂ) :
    rectHSNorm r (matrixRectangularUnitaryAction ρ U X - X) =
      rectHSNorm r (ρ U.val * X - X * (U.val : CMatrix d)) := by
  have hu : (U.val : CMatrix d) * (U.val : CMatrix d)ᴴ = 1 :=
    (matrixSubalgebraUnitary B U).prop.2
  have he : matrixRectangularUnitaryAction ρ U X - X =
      (ρ U.val * X - X * (U.val : CMatrix d)) * (U.val : CMatrix d)ᴴ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc X, hu, Matrix.mul_one]
    rfl
  rw [he]
  exact rectHSNorm_mul_unitary r _ (matrixSubalgebraUnitary B U)⁻¹

theorem matrixRectangularUnitaryAction_displacement_le (r : Nat) (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (U : unitary B) (X V : Matrix (Fin m) (Fin d) ℂ) :
    rectHSNorm r (matrixRectangularUnitaryAction ρ U X - V) ≤ rectHSNorm r (X - V) +
      rectHSNorm r (ρ U.val * V - V * (U.val : CMatrix d)) := by
  have he : matrixRectangularUnitaryAction ρ U X - V =
      matrixRectangularUnitaryAction ρ U (X - V) + (matrixRectangularUnitaryAction ρ U V - V) := by
    rw [map_sub]
    abel
  rw [he]
  exact (rectHSNorm_add_le r _ _).trans_eq (by
    rw [matrixRectangularUnitaryAction_hsNorm, matrixRectangularUnitaryAction_defect_norm])

def matrixRectangularIntertwiningConstraint (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (Y : Matrix (Fin m) (Fin d) ℂ) : B →ₗ[ℂ] Matrix (Fin m) (Fin d) ℂ where
  toFun X := ρ X * Y - Y * (X : CMatrix d)
  map_add' X Z := by
    change ρ (X + Z) * Y - Y * ((X : CMatrix d) + (Z : CMatrix d)) = _
    rw [map_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c X := by
    change ρ (c • X) * Y - Y * (c • (X : CMatrix d)) = _
    rw [map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rfl

theorem matrixRectangular_intertwines_of_unitaries (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (Y : Matrix (Fin m) (Fin d) ℂ)
    (hU : ∀ U : unitary B, ρ U.val * Y = Y * (U.val : CMatrix d)) :
    ∀ X : B, ρ X * Y = Y * (X : CMatrix d) := by
  let : IsClosed (B : Set (CMatrix d)) := B.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  let C := matrixRectangularIntertwiningConstraint ρ Y
  have hspan : Submodule.span ℂ (unitary B : Set B) ≤ LinearMap.ker C := by
    apply Submodule.span_le.mpr
    intro X hX
    exact sub_eq_zero.mpr (hU ⟨X, hX⟩)
  intro X
  have hx : X ∈ Submodule.span ℂ (unitary B : Set B) := by rw [CStarAlgebra.span_unitary]; trivial
  exact sub_eq_zero.mp (hspan hx)

noncomputable def matrixRectangularUnitaryActionHilbert (r : Nat) [NeZero r]
    (ρ : B →⋆ₐ[ℂ] CMatrix m) (U : unitary B) :
    FiniteRectMatrixHilbert r m d →ₗᵢ[ℂ] FiniteRectMatrixHilbert r m d where
  toLinearMap := (finiteRectMatrixHilbertEquiv r m d).toLinearMap.comp
    ((matrixRectangularUnitaryAction ρ U).comp (finiteRectMatrixHilbertEquiv r m d).symm.toLinearMap)
  norm_map' ξ := by
    obtain ⟨X, rfl⟩ := (finiteRectMatrixHilbertEquiv r m d).surjective ξ
    exact (finiteRectMatrixHilbert_norm r m d _).trans
      ((matrixRectangularUnitaryAction_hsNorm r ρ U X).trans (finiteRectMatrixHilbert_norm r m d X).symm)

end ThomGame.Analysis
