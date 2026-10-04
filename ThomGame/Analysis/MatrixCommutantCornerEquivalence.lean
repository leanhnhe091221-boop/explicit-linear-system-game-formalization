module

public import ThomGame.Analysis.MatrixIntertwinerCommutants
public import ThomGame.Analysis.MatrixPartialIsometryCorners

/-!
# Actual star algebra equivalence of commutant support corners

Conjugation by the given partial isometry and by its adjoint are inverse
on the two supported subalgebras. The target representation need not be faithful.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat} [NeZero d]
    (A : StarSubalgebra ℂ (CMatrix d))
    (ρ : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) →⋆ₐ[ℂ] CMatrix m)
    (W : Matrix (Fin m) (Fin d) ℂ) (hWi : IsStarProjection (Wᴴ * W))
    (hW : ∀ a : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)), ρ a * W = W * (a : CMatrix d))

include hW

omit [NeZero d] in
theorem matrixCommutantIntertwiner_push_corner (X : CMatrix d) (hX : X ∈ A) :
    W * X * Wᴴ ∈ matrixSubalgebraCorner
      (StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)))
      (W * Wᴴ) (matrixPartialIsometry_final_projection hWi) :=
  ⟨matrixCommutantIntertwiner_push_mem A ρ W hW X hX, matrixPartialIsometry_sandwich_support W hWi X⟩

theorem matrixCommutantIntertwiner_pull_corner (Y : CMatrix m)
    (hY : Y ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m))) :
    Wᴴ * Y * W ∈ matrixSubalgebraCorner A (Wᴴ * W) hWi := by
  refine ⟨matrixCommutantIntertwiner_pull_mem A ρ W hW Y hY, ?_⟩
  have hi : IsStarProjection (Wᴴᴴ * Wᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_final_projection hWi
  change (Wᴴ * W) * (Wᴴ * Y * W) = Wᴴ * Y * W ∧
    (Wᴴ * Y * W) * (Wᴴ * W) = Wᴴ * Y * W
  simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_sandwich_support Wᴴ hi Y

noncomputable def matrixCommutantCornerEquiv :
    matrixSubalgebraCorner A (Wᴴ * W) hWi ≃⋆ₐ[ℂ]
      matrixSubalgebraCorner (StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)))
        (W * Wᴴ) (matrixPartialIsometry_final_projection hWi) where
  toFun X := ⟨W * (X : CMatrix d) * Wᴴ, matrixCommutantIntertwiner_push_corner A ρ W hWi hW X X.property.1⟩
  invFun Y := ⟨Wᴴ * (Y : CMatrix m) * W, matrixCommutantIntertwiner_pull_corner A ρ W hWi hW Y Y.property.1⟩
  left_inv X := by
    apply Subtype.ext
    exact matrixSandwich_inverse_of_support W X X.property.2.1 X.property.2.2
  right_inv Y := by
    apply Subtype.ext
    have he := matrixSandwich_inverse_of_support Wᴴ (Y : CMatrix m)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using Y.property.2.1)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using Y.property.2.2)
    simpa only [Matrix.conjTranspose_conjTranspose] using he
  map_mul' X Y := by
    apply Subtype.ext
    exact (matrixSandwich_mul_of_support W X Y Y.property.2.1).symm
  map_add' X Y := by
    apply Subtype.ext
    change W * ((X : CMatrix d) + (Y : CMatrix d)) * Wᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_star' X := by
    apply Subtype.ext
    change W * (X : CMatrix d)ᴴ * Wᴴ = (W * (X : CMatrix d) * Wᴴ)ᴴ
    exact (matrixSandwich_star W X).symm
  map_smul' c X := by
    apply Subtype.ext
    change W * (c • (X : CMatrix d)) * Wᴴ = c • (W * (X : CMatrix d) * Wᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]

theorem matrixCommutantCornerEquiv_apply
    (X : matrixSubalgebraCorner A (Wᴴ * W) hWi) :
    (matrixCommutantCornerEquiv A ρ W hWi hW X : CMatrix m) = W * (X : CMatrix d) * Wᴴ := rfl

theorem matrixCommutantCornerEquiv_image :
    (fun X : CMatrix d => W * X * Wᴴ) '' (matrixSubalgebraCorner A (Wᴴ * W) hWi : Set (CMatrix d)) =
      (matrixSubalgebraCorner (StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)))
        (W * Wᴴ) (matrixPartialIsometry_final_projection hWi) : Set (CMatrix m)) := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact matrixCommutantIntertwiner_push_corner A ρ W hWi hW X hX.1
  · intro hY
    let E := matrixCommutantCornerEquiv A ρ W hWi hW
    exact ⟨E.symm ⟨Y, hY⟩, (E.symm ⟨Y, hY⟩).property,
      congrArg Subtype.val (E.apply_symm_apply ⟨Y, hY⟩)⟩

end ThomGame.Analysis
