module

public import ThomGame.Analysis.MatrixSelfAdjointDilation
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing doubled matrices without changing Hilbert--Schmidt mass

The sum-indexed block matrices are transported to the project's actual
Fin-indexed matrix type. Reindexing preserves the algebra, adjoint and
all rectangular Hilbert--Schmidt norms with a fixed normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

theorem rectHSNorm_reindex (r : Nat) (e : ι ≃ ι') (f : κ ≃ κ') (A : Matrix ι κ ℂ) :
    rectHSNorm r (Matrix.reindex e f A) = rectHSNorm r A := by
  have he : rectHSNorm r (Matrix.reindex e f A) ^ 2 = rectHSNorm r A ^ 2 := by
    simp only [rectHSNorm_sq, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [e.symm.sum_comp (fun i => ∑ j, ‖A i (f.symm j)‖ ^ 2)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact f.symm.sum_comp (fun j => ‖A i j‖ ^ 2)
  nlinarith [rectHSNorm_nonneg r (Matrix.reindex e f A), rectHSNorm_nonneg r A]

variable (d : Nat)

noncomputable def matrixSumReindex :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ ≃⋆ₐ[ℝ] CMatrix (d + d) where
  __ := Matrix.reindexAlgEquiv ℝ ℂ finSumFinEquiv
  map_smul' _ _ := rfl
  map_star' A := by
    exact (Matrix.conjTranspose_reindex finSumFinEquiv finSumFinEquiv A).symm

noncomputable def matrixDoubleBlocks (A B C D : CMatrix d) : CMatrix (d + d) :=
  matrixSumReindex d (Matrix.fromBlocks A B C D)

theorem matrixSumReindex_rectHSNorm (r : Nat) (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) :
    rectHSNorm r (matrixSumReindex d A) = rectHSNorm r A :=
  rectHSNorm_reindex r finSumFinEquiv finSumFinEquiv A

theorem matrixDoubleBlocks_star (A B C D : CMatrix d) :
    star (matrixDoubleBlocks d A B C D) = matrixDoubleBlocks d (star A) (star C) (star B) (star D) := by
  rw [matrixDoubleBlocks, ← map_star]
  congr 1
  ext (i | i) (j | j) <;> rfl

theorem matrixDoubleBlocks_mul (A B C D E F G H : CMatrix d) :
    matrixDoubleBlocks d A B C D * matrixDoubleBlocks d E F G H =
      matrixDoubleBlocks d (A * E + B * G) (A * F + B * H) (C * E + D * G) (C * F + D * H) := by
  rw [matrixDoubleBlocks, matrixDoubleBlocks, ← map_mul, Matrix.fromBlocks_multiply]
  rfl

theorem matrixDoubleBlocks_sub (A B C D E F G H : CMatrix d) :
    matrixDoubleBlocks d A B C D - matrixDoubleBlocks d E F G H =
      matrixDoubleBlocks d (A - E) (B - F) (C - G) (D - H) := by
  rw [matrixDoubleBlocks, matrixDoubleBlocks, ← map_sub]
  congr 1
  ext (i | i) (j | j) <;> rfl

theorem matrixDoubleBlocks_one : matrixDoubleBlocks d 1 0 0 1 = 1 := by
  rw [matrixDoubleBlocks, Matrix.fromBlocks_one, map_one]

theorem matrixDoubleBlocks_hsNorm_sq [NeZero d] (A B C D : CMatrix d) :
    hsNorm (matrixDoubleBlocks d A B C D) ^ 2 =
      (hsNorm A ^ 2 + hsNorm B ^ 2 + hsNorm C ^ 2 + hsNorm D ^ 2) / 2 := by
  rw [← rectHSNorm_eq_hsNorm, matrixDoubleBlocks, matrixSumReindex_rectHSNorm,
    rectHSNorm_fromBlocks_sq]
  simp only [rectHSNorm_sq, hsNorm_sq, Nat.cast_add]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp
  ring

end ThomGame.Analysis
