module

public import ThomGame.Analysis.MatrixBoundedScaleRatioIdentity
public import ThomGame.Analysis.RectangularOperatorBounds

/-!
# A uniform norm bound from concentration at one half

The estimate uses a polynomial identity and two contraction bounds.
All rectangular Hilbert--Schmidt norms keep the supplied denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixRatioDefect_center_identity {d : Nat} (D X Y : CMatrix d)
    (h : D * Y * (1 - X) = Y - X) :
    (1 / 4 : ℂ) • D = (Y - X) - D * (Y - (1 / 2 : ℂ) • 1) * (1 - X) +
      (1 / 2 : ℂ) • (D * (X - (1 / 2 : ℂ) • 1)) := by
  rw [← h]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  module

theorem matrixRatioDefect_center_bound {d : Nat} (r : Nat) (D X Y : CMatrix d)
    (hD : ‖D‖ ≤ 1) (hX : ‖1 - X‖ ≤ 1) (h : D * Y * (1 - X) = Y - X) :
    rectHSNorm r D ≤ 8 * (rectHSNorm r (X - (1 / 2 : ℂ) • 1) +
      rectHSNorm r (Y - (1 / 2 : ℂ) • 1)) := by
  have hDX : rectHSNorm r (D * (X - (1 / 2 : ℂ) • 1)) ≤
      rectHSNorm r (X - (1 / 2 : ℂ) • 1) :=
    (rectHSNorm_mul_le_left r _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (rectHSNorm_nonneg _ _))
  have hDY : rectHSNorm r (D * (Y - (1 / 2 : ℂ) • 1) * (1 - X)) ≤
      rectHSNorm r (Y - (1 / 2 : ℂ) • 1) := by
    apply (rectHSNorm_mul_le_right r _ _).trans
    calc
      _ ≤ rectHSNorm r (D * (Y - (1 / 2 : ℂ) • 1)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (rectHSNorm_nonneg _ _)
      _ ≤ _ := (rectHSNorm_mul_le_left r _ _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (rectHSNorm_nonneg _ _))
  have hYX : rectHSNorm r (Y - X) ≤ rectHSNorm r (Y - (1 / 2 : ℂ) • 1) +
      rectHSNorm r (X - (1 / 2 : ℂ) • 1) := by
    convert rectHSNorm_sub_le r (Y - (1 / 2 : ℂ) • 1) (X - (1 / 2 : ℂ) • 1) using 1
    congr 1
    abel
  have he := rectHSNorm_add_le r
    ((Y - X) - D * (Y - (1 / 2 : ℂ) • 1) * (1 - X))
    ((1 / 2 : ℂ) • (D * (X - (1 / 2 : ℂ) • 1)))
  rw [← matrixRatioDefect_center_identity D X Y h, rectHSNorm_smul, rectHSNorm_smul] at he
  have ht := rectHSNorm_sub_le r (Y - X) (D * (Y - (1 / 2 : ℂ) • 1) * (1 - X))
  norm_num at he
  nlinarith [rectHSNorm_nonneg r (X - (1 / 2 : ℂ) • 1)]

end ThomGame.Analysis
