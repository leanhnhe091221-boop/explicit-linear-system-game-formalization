module

public import ThomGame.Analysis.MatrixProjectionFrames

/-!
# Actual partial isometries between equal-rank projections

The rectangular map is formed from the two orthonormal eigenvector
frames and a bijection of their nonzero eigenvalue index sets.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem exists_matrixPartialIsometry_of_rank_eq {P : Matrix κ κ ℂ} {Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hrank : P.rank = Q.rank) :
    ∃ W : Matrix ι κ ℂ, Wᴴ * W = P ∧ W * Wᴴ = Q := by
  classical
  let α := {i // hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0}
  let β := {i // hQ.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0}
  have hcard : Fintype.card α = Fintype.card β := by
    rw [← hP.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs,
      ← hQ.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs]
    exact hrank
  let e : α ≃ β := Fintype.equivOfCardEq hcard
  let F := matrixProjectionFrame hP
  let G := (matrixProjectionFrame hQ).submatrix id e
  have hFi : Fᴴ * F = 1 := matrixProjectionFrame_initial hP
  have hFf : F * Fᴴ = P := matrixProjectionFrame_final hP
  have hGi : Gᴴ * G = 1 := by
    dsimp only [G]
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul _ _ e id e Function.bijective_id,
      matrixProjectionFrame_initial hQ, Matrix.submatrix_one_equiv]
  have hGf : G * Gᴴ = Q := by
    dsimp only [G]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      matrixProjectionFrame_final hQ, Matrix.submatrix_id_id]
  refine ⟨G * Fᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (F * Gᴴ) * (G * Fᴴ) = F * (Gᴴ * G) * Fᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hGi, Matrix.mul_one, hFf]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (G * Fᴴ) * (F * Gᴴ) = G * (Fᴴ * F) * Gᴴ := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hFi, Matrix.mul_one, hGf]

omit [DecidableEq ι] in
theorem matrixPartialIsometry_mul_initial {W : Matrix ι κ ℂ}
    (hW : IsStarProjection (Wᴴ * W)) : W * (Wᴴ * W) = W := by
  have he := matrix_mul_absSupport W
  rwa [matrixRectAbs_of_initial_projection hW, matrixRealSupport_projection hW] at he

omit [DecidableEq ι] in
theorem matrixPartialIsometry_final_projection {W : Matrix ι κ ℂ}
    (hW : IsStarProjection (Wᴴ * W)) : IsStarProjection (W * Wᴴ) := by
  have he := matrixRectPolar_final_projection W
  rwa [matrixRectPolar_of_initial_projection hW] at he

end ThomGame.Analysis
