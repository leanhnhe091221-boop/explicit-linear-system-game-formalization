module

public import ThomGame.Analysis.FiniteMatrixHilbert

/-!
# Unitary conjugation in the matrix algebra and trace Hilbert space

Conjugation preserves both actual matrix norms and the normalized trace.
Its trace adjoint is conjugation by the inverse unitary. The difference
from the identity has the same trace norm as the actual commutator.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat}

def matrixUnitaryConjugation (U : UnitaryMatrix d) : CMatrix d →ₗ[ℂ] CMatrix d :=
  (LinearMap.mulRight ℂ (star U.val)).comp (LinearMap.mulLeft ℂ U.val)

@[simp] theorem matrixUnitaryConjugation_apply (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryConjugation U X = U.val * X * star U.val := rfl

@[simp] theorem matrixUnitaryConjugation_one (U : UnitaryMatrix d) :
    matrixUnitaryConjugation U 1 = 1 := by
  simpa only [matrixUnitaryConjugation_apply, mul_one] using U.prop.2

@[simp] theorem matrixUnitaryConjugation_star (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryConjugation U (star X) = star (matrixUnitaryConjugation U X) := by
  simp only [matrixUnitaryConjugation_apply, star_mul, star_star, mul_assoc]

theorem matrixUnitaryConjugation_inv (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryConjugation U⁻¹ (matrixUnitaryConjugation U X) = X := by
  simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.inv_val, star_star]
  calc
    _ = (star U.val * U.val) * X * (star U.val * U.val) := by simp only [mul_assoc]
    _ = X := by rw [U.prop.1, one_mul, mul_one]

@[simp] theorem matrixUnitaryConjugation_matrixOpNorm (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixOpNorm (matrixUnitaryConjugation U X) = matrixOpNorm X := by
  change ‖U.val * X * (U⁻¹).val‖ = ‖X‖
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

@[simp] theorem matrixUnitaryConjugation_hsNorm (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (matrixUnitaryConjugation U X) = hsNorm X := by
  change hsNorm (U.val * X * (U⁻¹).val) = hsNorm X
  rw [hsNorm_mul_unitary, hsNorm_unitary_mul]

@[simp] theorem matrixUnitaryConjugation_trace (U : UnitaryMatrix d) (X : CMatrix d) :
    normalizedTrace (matrixUnitaryConjugation U X) = normalizedTrace X := by
  rw [matrixUnitaryConjugation_apply, normalizedTrace_mul_comm, ← mul_assoc, U.prop.1, one_mul]

theorem matrixUnitaryConjugation_pairing (U : UnitaryMatrix d) (X Y : CMatrix d) :
    normalizedTrace (star (matrixUnitaryConjugation U X) * Y) =
      normalizedTrace (star X * matrixUnitaryConjugation U⁻¹ Y) := by
  simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.inv_val, star_mul, star_star]
  change normalizedTrace ((U.val * (star X * star U.val)) * Y) =
    normalizedTrace (star X * (star U.val * Y * U.val))
  rw [mul_assoc, normalizedTrace_mul_comm U.val]
  simp only [mul_assoc]

theorem matrixUnitaryConjugation_sub_hsNorm (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (matrixUnitaryConjugation U X - X) = hsNorm (U.val * X - X * U.val) := by
  have he : matrixUnitaryConjugation U X - X = (U.val * X - X * U.val) * (U⁻¹).val := by
    change U.val * X * star U.val - X = (U.val * X - X * U.val) * star U.val
    rw [sub_mul, mul_assoc X, U.prop.2, mul_one]
  rw [he, hsNorm_mul_unitary]

variable [NeZero d]

noncomputable def matrixConjugationHilbert (U : UnitaryMatrix d) :
    FiniteMatrixHilbert d →ₗᵢ[ℂ] FiniteMatrixHilbert d where
  toLinearMap := (finiteMatrixHilbertEquiv d).toLinearMap.comp
    ((matrixUnitaryConjugation U).comp (finiteMatrixHilbertEquiv d).symm.toLinearMap)
  norm_map' ξ := by
    obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
    exact (finiteMatrixHilbert_norm d _).trans
      ((matrixUnitaryConjugation_hsNorm U X).trans (finiteMatrixHilbert_norm d X).symm)

@[simp] theorem matrixConjugationHilbert_embedding (U : UnitaryMatrix d) (X : CMatrix d) :
    matrixConjugationHilbert U (finiteMatrixHilbertEquiv d X) =
      finiteMatrixHilbertEquiv d (matrixUnitaryConjugation U X) := rfl

theorem matrixConjugationHilbert_pairing (U : UnitaryMatrix d) (ξ η : FiniteMatrixHilbert d) :
    inner ℂ (matrixConjugationHilbert U ξ) η = inner ℂ ξ (matrixConjugationHilbert U⁻¹ η) := by
  obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
  obtain ⟨Y, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective η
  exact matrixUnitaryConjugation_pairing U X Y

theorem matrixConjugationHilbert_sub_norm (U : UnitaryMatrix d) (X : CMatrix d) :
    ‖matrixConjugationHilbert U (finiteMatrixHilbertEquiv d X) - finiteMatrixHilbertEquiv d X‖ =
      hsNorm (U.val * X - X * U.val) := by
  rw [matrixConjugationHilbert_embedding, ← map_sub, finiteMatrixHilbert_norm,
    matrixUnitaryConjugation_sub_hsNorm]

noncomputable def matrixConjugationHilbertEquiv (U : UnitaryMatrix d) :
    FiniteMatrixHilbert d ≃ₗᵢ[ℂ] FiniteMatrixHilbert d where
  __ := matrixConjugationHilbert U
  invFun := matrixConjugationHilbert U⁻¹
  left_inv ξ := by
    obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
    change finiteMatrixHilbertEquiv d (matrixUnitaryConjugation U⁻¹ (matrixUnitaryConjugation U X)) =
      finiteMatrixHilbertEquiv d X
    rw [matrixUnitaryConjugation_inv]
  right_inv ξ := by
    obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
    change finiteMatrixHilbertEquiv d (matrixUnitaryConjugation U (matrixUnitaryConjugation U⁻¹ X)) =
      finiteMatrixHilbertEquiv d X
    simpa only [inv_inv] using
      congrArg (finiteMatrixHilbertEquiv d) (matrixUnitaryConjugation_inv U⁻¹ X)

@[simp] theorem matrixConjugationHilbertEquiv_apply (U : UnitaryMatrix d) (ξ : FiniteMatrixHilbert d) :
    matrixConjugationHilbertEquiv U ξ = matrixConjugationHilbert U ξ := rfl

@[simp] theorem matrixConjugationHilbertEquiv_symm_apply (U : UnitaryMatrix d) (ξ : FiniteMatrixHilbert d) :
    (matrixConjugationHilbertEquiv U).symm ξ = matrixConjugationHilbert U⁻¹ ξ := rfl

end ThomGame.Analysis
