module

public import ThomGame.Analysis.MatrixProjectionSubrank

/-!
# Orthonormal matrix frames for actual projection ranges

The nonzero eigenvectors of a projection form a rectangular matrix
with initial identity and final projection equal to the given matrix.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixProjectionFrame {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    Matrix ι {i // hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0} ℂ :=
  hP.isSelfAdjoint.isHermitian.eigenvectorUnitary.val.submatrix id Subtype.val

theorem matrixProjectionFrame_initial {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    (matrixProjectionFrame hP)ᴴ * matrixProjectionFrame hP = 1 := by
  have hU : hP.isSelfAdjoint.isHermitian.eigenvectorUnitary.valᴴ *
      hP.isSelfAdjoint.isHermitian.eigenvectorUnitary.val = 1 :=
    hP.isSelfAdjoint.isHermitian.eigenvectorUnitary.prop.1
  rw [matrixProjectionFrame, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ Subtype.val id Subtype.val Function.bijective_id,
    hU,
    Matrix.submatrix_one _ Subtype.val_injective]

theorem matrixProjectionFrame_final {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    matrixProjectionFrame hP * (matrixProjectionFrame hP)ᴴ = P := by
  classical
  let H := hP.isSelfAdjoint.isHermitian
  conv_rhs => rw [H.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext i j
  change (∑ k : {i // H.eigenvalues i ≠ 0}, H.eigenvectorUnitary.val i k.val *
    star (H.eigenvectorUnitary.val j k.val)) =
    ∑ k, (H.eigenvectorUnitary.val * Matrix.diagonal (fun k => (H.eigenvalues k : ℂ))) i k *
      star (H.eigenvectorUnitary.val j k)
  simp only [Matrix.mul_diagonal]
  have he (k : ι) : H.eigenvectorUnitary.val i k * (↑(H.eigenvalues k) : ℂ) *
      star (H.eigenvectorUnitary.val j k) =
      if H.eigenvalues k ≠ 0 then H.eigenvectorUnitary.val i k * star (H.eigenvectorUnitary.val j k) else 0 := by
    rcases matrixProjection_eigenvalues_mem hP k with hk | hk <;> simp [hk]
  change (∑ k : {i // H.eigenvalues i ≠ 0}, H.eigenvectorUnitary.val i k.val *
    star (H.eigenvectorUnitary.val j k.val)) =
    ∑ k, H.eigenvectorUnitary.val i k * (↑(H.eigenvalues k) : ℂ) * star (H.eigenvectorUnitary.val j k)
  simp_rw [he]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun k => H.eigenvalues k ≠ 0))
    (by simp) (fun k => H.eigenvectorUnitary.val i k * star (H.eigenvectorUnitary.val j k))).symm

end ThomGame.Analysis
