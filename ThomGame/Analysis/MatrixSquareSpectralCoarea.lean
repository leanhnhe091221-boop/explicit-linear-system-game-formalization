module

public import ThomGame.Analysis.SquareSpectralCoarea
public import ThomGame.Analysis.MatrixSpectralCut
public import ThomGame.Analysis.MatrixIntertwinerSpectral
public import Mathlib.Analysis.Matrix.Order

/-! Connes' joint-distribution estimate for actual finite matrix spectral projections. -/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def matrixSquareSpectralCut {d : Nat} (A : CMatrix d) (s : ℝ) : CMatrix d :=
  cfc (fun t : ℝ => spectralStep s (t ^ 2)) A

theorem matrixSquareSpectralCut_eq_sqrt_cut {d : Nat} {A : CMatrix d}
    (hA : 0 ≤ A) (s : ℝ) : matrixSquareSpectralCut A s = matrixSpectralCut A (Real.sqrt s) := by
  unfold matrixSquareSpectralCut matrixSpectralCut
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  simp only [spectralStep, Real.sqrt_le_iff, hx0, true_and]

theorem matrixSquareSpectralCut_isStarProjection {d : Nat} {A : CMatrix d}
    (hA : Matrix.IsHermitian A) (s : ℝ) : IsStarProjection (matrixSquareSpectralCut A s) := by
  rw [matrixSquareSpectralCut, matrix_cfc_conjugate hA]
  exact (matrix_diagonal_spectralStep_projection (fun i => hA.eigenvalues i ^ 2) s).map
    (Unitary.conjStarAlgAut ℂ (CMatrix d) hA.eigenvectorUnitary)

theorem matrixSquareSpectralCut_intertwiner_sq {d e : Nat} {A : CMatrix d} {B : CMatrix e}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix (Fin d) (Fin e) ℂ) (s : ℝ) :
    rectHSNorm 1 (matrixSquareSpectralCut A s * X - X * matrixSquareSpectralCut B s) ^ 2 =
      ∑ i, ∑ j, ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j‖ ^ 2 *
        (spectralStep s (hA.eigenvalues i ^ 2) - spectralStep s (hB.eigenvalues j ^ 2)) ^ 2 := by
  simp only [matrixSquareSpectralCut, rectHSNorm_cfc_intertwiner_sq 1 hA hB, Nat.cast_one, div_one]

theorem matrixIntertwiner_plus_spectral_sq {d e : Nat} {A : CMatrix d} {B : CMatrix e}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix (Fin d) (Fin e) ℂ) :
    rectHSNorm 1 (A * X + X * B) ^ 2 =
      ∑ i, ∑ j, ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j‖ ^ 2 *
        (hA.eigenvalues i + hB.eigenvalues j) ^ 2 := by
  have he := rectHSNorm_cfc_intertwiner_sq 1 hA hB (fun t => t) (fun t => -t) X
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  simpa only [hid, cfc_neg_id B hB.isSelfAdjoint, Matrix.mul_neg, sub_neg_eq_add,
    Nat.cast_one, div_one] using he

theorem matrixSquareSpectralCut_intertwiner_integrable {d e : Nat} {A : CMatrix d} {B : CMatrix e}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix (Fin d) (Fin e) ℂ) :
    Integrable (fun s => rectHSNorm 1
      (matrixSquareSpectralCut A s * X - X * matrixSquareSpectralCut B s) ^ 2) := by
  have he : (fun s => rectHSNorm 1
      (matrixSquareSpectralCut A s * X - X * matrixSquareSpectralCut B s) ^ 2) =
      (fun s => ∑ p : Fin d × Fin e,
        ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X p.1 p.2‖ ^ 2 *
          (spectralStep s (hA.eigenvalues p.1 ^ 2) - spectralStep s (hB.eigenvalues p.2 ^ 2)) ^ 2) := by
    funext s
    rw [matrixSquareSpectralCut_intertwiner_sq hA hB, Fintype.sum_prod_type]
  rw [he]
  exact weighted_squareSteps_integrable _ _ _

theorem matrixSquareSpectralCut_intertwiner_coarea {d e : Nat} {A : CMatrix d} {B : CMatrix e}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix (Fin d) (Fin e) ℂ) :
    (∫ s, rectHSNorm 1 (matrixSquareSpectralCut A s * X - X * matrixSquareSpectralCut B s) ^ 2) ≤
      rectHSNorm 1 (A * X - X * B) * rectHSNorm 1 (A * X + X * B) := by
  have h := weighted_squareSteps_coarea
    (fun p : Fin d × Fin e =>
      ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X p.1 p.2‖ ^ 2)
    (fun p => hB.eigenvalues p.2) (fun p => hA.eigenvalues p.1) (fun _ => sq_nonneg _)
  simp only [Fintype.sum_prod_type, ← matrixSquareSpectralCut_intertwiner_sq hA hB,
    ← matrixIntertwiner_plus_spectral_sq hA hB] at h
  have hm := rectHSNorm_intertwiner_spectral_sq 1 hA hB X
  simp only [Nat.cast_one, div_one] at hm
  rw [← hm, Real.sqrt_sq (rectHSNorm_nonneg _ _), Real.sqrt_sq (rectHSNorm_nonneg _ _)] at h
  exact h

theorem matrixSquareSpectralCut_unitary_coarea {d : Nat} {A : CMatrix d}
    (hA : Matrix.IsHermitian A) (U : UnitaryMatrix d) :
    (∫ s, rectHSNorm 1 (matrixSquareSpectralCut A s * U.val -
      U.val * matrixSquareSpectralCut A s) ^ 2) ≤
      2 * rectHSNorm 1 A * rectHSNorm 1 (A * U.val - U.val * A) := by
  have h := matrixSquareSpectralCut_intertwiner_coarea hA hA U.val
  have hp := rectHSNorm_add_le 1 (A * U.val) (U.val * A)
  rw [rectHSNorm_mul_unitary, rectHSNorm_unitary_mul] at hp
  have hb := mul_le_mul_of_nonneg_left hp (rectHSNorm_nonneg 1 (A * U.val - U.val * A))
  exact h.trans (by nlinarith only [hb])

end ThomGame.Analysis
