module

public import ThomGame.Analysis.MatrixIntertwinerSpectral

/-!
# Functional calculus across rectangular intertwiners

An exact intertwiner between Hermitian matrices intertwines every real
function on their finite spectra. No global continuity is required.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixIntertwinerBasis_eq_zero (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) {X : Matrix ι κ ℂ}
    (hX : matrixIntertwinerBasis U V X = 0) : X = 0 := by
  apply (rectHSNorm_eq_zero_iff (by decide : 0 < 1) X).mp
  rw [← rectHSNorm_intertwiner_basis 1 U V X, hX, rectHSNorm_zero]

theorem matrix_cfc_intertwine {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f : ℝ → ℝ) (X : Matrix ι κ ℂ) (hX : A * X = X * B) :
    cfc f A * X = X * cfc f B := by
  have hidA : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  have hidB : cfc (fun t : ℝ => t) B = B := cfc_id ℝ B
  have hd : Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X -
      matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X *
      Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) = 0 := by
    rw [← matrixIntertwinerBasis_cfc hA hB (fun t => t) (fun t => t), hidA, hidB, hX, sub_self]
    simp [matrixIntertwinerBasis]
  apply sub_eq_zero.mp
  apply matrixIntertwinerBasis_eq_zero hA.eigenvectorUnitary hB.eigenvectorUnitary
  rw [matrixIntertwinerBasis_cfc hA hB]
  ext i j
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hab : hA.eigenvalues i = hB.eigenvalues j
  · rw [hab, mul_comm, sub_self]
  · have hij := congrFun (congrFun hd i) j
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at hij
    have hn : (hA.eigenvalues i : ℂ) - (hB.eigenvalues j : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hab)
    have hz : matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j = 0 := by
      apply (mul_eq_zero.mp (show ((hA.eigenvalues i : ℂ) - (hB.eigenvalues j : ℂ)) *
        matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j = 0 from ?_)).resolve_left hn
      simpa only [sub_mul, mul_comm (hB.eigenvalues j : ℂ)] using hij
    rw [hz, mul_zero, zero_mul, sub_self]

end ThomGame.Analysis
