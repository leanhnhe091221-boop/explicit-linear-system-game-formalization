module

public import ThomGame.Analysis.MatrixPolarSupport
public import ThomGame.Analysis.MatrixPolarLipschitz

/-!
# Polar continuity from actual singular-value bounds

A lower bound on the nonzero eigenvalues of |X| implies the required
gap for the self-adjoint dilation. Thus the polar Lipschitz theorem
uses the usual nonzero singular values, without an extra certificate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixRealSupport_cfc_abs {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealSupport (cfc (abs : ℝ → ℝ) A) = matrixRealSupport A := by
  rw [matrixRealSupport, ← cfc_comp' (fun t : ℝ => if t = 0 then 0 else 1) abs A
    ((A.finite_real_spectrum.image abs).continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint]
  apply cfc_congr
  intro t _
  simp only [abs_eq_zero]

theorem matrixRealSupport_lower_abs_iff {A : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (b : ℝ) :
    b • matrixRealSupport A ≤ cfc (abs : ℝ → ℝ) A ↔
      ∀ t ∈ spectrum ℝ A, t = 0 ∨ b ≤ |t| := by
  rw [matrixRealSupport, ← cfc_const_mul b _ A (A.finite_real_spectrum.continuousOn _),
    cfc_le_iff _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  by_cases ht : t = 0 <;> simp [ht]

theorem matrixRealSupport_lower_iff {A : Matrix ι ι ℂ} (hA : 0 ≤ A) (b : ℝ) :
    b • matrixRealSupport A ≤ A ↔ ∀ t ∈ spectrum ℝ A, t = 0 ∨ b ≤ t := by
  have hid : cfc (abs : ℝ → ℝ) A = A := by
    calc
      _ = cfc (fun t : ℝ => t) A := cfc_congr fun t ht =>
        abs_of_nonneg (spectrum_nonneg_of_nonneg hA ht)
      _ = A := cfc_id ℝ A
  have he := matrixRealSupport_lower_abs_iff hA.isSelfAdjoint.isHermitian b
  rw [hid] at he
  rw [he]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  rw [abs_of_nonneg (spectrum_nonneg_of_nonneg hA ht)]

theorem matrixHasPolarGap_of_support_lower {X : Matrix ι κ ℂ} {b : ℝ}
    (hX : b • matrixRealSupport (matrixRectAbs X) ≤ matrixRectAbs X) : MatrixHasPolarGap b X := by
  apply (matrixRealSupport_lower_abs_iff (matrixSelfAdjointDilation_isHermitian X) b).mp
  rw [← matrixRealSupport_cfc_abs (matrixSelfAdjointDilation_isHermitian X),
    matrixSelfAdjointDilation_cfc_abs, matrixRealSupport,
    matrix_cfc_blockDiagonal (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)]
  have hleft := matrixRectAbs_support_lower_adjoint X b hX
  apply sub_nonneg.mp
  have he := matrix_fromBlocks_diagonal_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hX)
  convert he using 1
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, matrixRealSupport]

theorem matrixHasPolarGap_of_singularValues {X : Matrix ι κ ℂ} {b : ℝ}
    (hX : ∀ t ∈ spectrum ℝ (matrixRectAbs X), t = 0 ∨ b ≤ t) : MatrixHasPolarGap b X :=
  matrixHasPolarGap_of_support_lower ((matrixRealSupport_lower_iff (matrixRectAbs_nonneg X) b).mpr hX)

theorem rectHSNorm_polar_sub_le_of_singularValues (r : Nat) {X Y : Matrix ι κ ℂ} {b : ℝ}
    (hb : 0 < b)
    (hX : ∀ t ∈ spectrum ℝ (matrixRectAbs X), t = 0 ∨ b ≤ t)
    (hY : ∀ t ∈ spectrum ℝ (matrixRectAbs Y), t = 0 ∨ b ≤ t) :
    rectHSNorm r (matrixRectPolar X - matrixRectPolar Y) ≤ b⁻¹ * rectHSNorm r (X - Y) :=
  rectHSNorm_polar_sub_le r hb (matrixHasPolarGap_of_singularValues hX)
    (matrixHasPolarGap_of_singularValues hY)

end ThomGame.Analysis
