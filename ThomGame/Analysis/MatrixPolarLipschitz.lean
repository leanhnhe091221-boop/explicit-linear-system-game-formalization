module

public import ThomGame.Analysis.MatrixPolarDilation
public import ThomGame.Analysis.MatrixFunctionalCalculusEnergy

/-!
# Hilbert--Schmidt continuity of the actual polar map

A spectral gap away from zero gives the exact constant b inverse.
The norm keeps the original normalization, including on the dilation.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def realClippedSign (b t : ℝ) : ℝ := realNormClamp 1 (t / b)

theorem realClippedSign_bound {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    |realClippedSign b s - realClippedSign b t| ≤ b⁻¹ * |s - t| := by
  have he : |realNormClamp 1 (s / b) - realNormClamp 1 (t / b)| ≤ |s / b - t / b| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (realNormClamp_lipschitz 1).dist_le_mul (s / b) (t / b)
  calc
    _ ≤ |s / b - t / b| := he
    _ = b⁻¹ * |s - t| := by
      rw [← sub_div, abs_div, abs_of_pos hb, div_eq_mul_inv, mul_comm]

theorem realClippedSign_eq_sign {b t : ℝ} (hb : 0 < b) (ht : t = 0 ∨ b ≤ |t|) :
    realClippedSign b t = t * |t|⁻¹ := by
  rcases ht with rfl | ht
  · norm_num [realClippedSign, realNormClamp]
  · rcases le_total 0 t with hp | hn
    · rw [abs_of_nonneg hp] at ht ⊢
      have ht0 : t ≠ 0 := ne_of_gt (hb.trans_le ht)
      have hdiv : 1 ≤ t / b := (le_div_iff₀ hb).mpr (by simpa using ht)
      simp [realClippedSign, realNormClamp, min_eq_left hdiv, mul_inv_cancel₀ ht0]
    · rw [abs_of_nonpos hn] at ht ⊢
      have ht0 : t ≠ 0 := by linarith
      have hdiv : t / b ≤ -1 := (div_le_iff₀ hb).mpr (by linarith)
      rw [inv_neg, mul_neg, mul_inv_cancel₀ ht0]
      unfold realClippedSign realNormClamp
      rw [min_eq_right (hdiv.trans (by norm_num : (-1 : ℝ) ≤ 1)), max_eq_left hdiv]

theorem matrixRealSign_eq_clipped {A : Matrix ι ι ℂ} {b : ℝ} (hb : 0 < b)
    (hgap : ∀ t ∈ spectrum ℝ A, t = 0 ∨ b ≤ |t|) :
    matrixRealSign A = cfc (realClippedSign b) A := by
  apply cfc_congr
  intro t ht
  exact (realClippedSign_eq_sign hb (hgap t ht)).symm

theorem rectHSNorm_sign_sub_le (r : Nat) {A B : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) {b : ℝ} (hb : 0 < b)
    (hgapA : ∀ t ∈ spectrum ℝ A, t = 0 ∨ b ≤ |t|)
    (hgapB : ∀ t ∈ spectrum ℝ B, t = 0 ∨ b ≤ |t|) :
    rectHSNorm r (matrixRealSign A - matrixRealSign B) ≤ b⁻¹ * rectHSNorm r (A - B) := by
  rw [matrixRealSign_eq_clipped hb hgapA, matrixRealSign_eq_clipped hb hgapB]
  exact rectHSNorm_cfc_sub_le r hA hB (realClippedSign b) (inv_nonneg.mpr hb.le)
    (realClippedSign_bound hb)

def MatrixHasPolarGap (b : ℝ) (X : Matrix ι κ ℂ) : Prop :=
  ∀ t ∈ spectrum ℝ (matrixSelfAdjointDilation X), t = 0 ∨ b ≤ |t|

theorem rectHSNorm_polar_sub_le (r : Nat) {X Y : Matrix ι κ ℂ} {b : ℝ}
    (hb : 0 < b) (hX : MatrixHasPolarGap b X) (hY : MatrixHasPolarGap b Y) :
    rectHSNorm r (matrixRectPolar X - matrixRectPolar Y) ≤ b⁻¹ * rectHSNorm r (X - Y) := by
  have he := rectHSNorm_sign_sub_le r (matrixSelfAdjointDilation_isHermitian X)
    (matrixSelfAdjointDilation_isHermitian Y) hb hX hY
  rw [matrixSelfAdjointDilation_sign, matrixSelfAdjointDilation_sign,
    ← matrixSelfAdjointDilation_sub, ← matrixSelfAdjointDilation_sub] at he
  have hs := mul_self_le_mul_self (rectHSNorm_nonneg _ _) he
  simp only [← pow_two, mul_pow, rectHSNorm_selfAdjointDilation_sq] at hs
  have hp := rectHSNorm_nonneg r (matrixRectPolar X - matrixRectPolar Y)
  have hq := mul_nonneg (inv_nonneg.mpr hb.le) (rectHSNorm_nonneg r (X - Y))
  nlinarith

end ThomGame.Analysis
