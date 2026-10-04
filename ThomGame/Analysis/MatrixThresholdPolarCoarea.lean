module

public import ThomGame.Analysis.MatrixSignedSpectralCoarea

/-!
# Coarea for rectangular threshold polar factors

The two dilation corners have identical squared HS norms. Together
with the total dimension bound this gives a uniform integral bound
for differences of the actual threshold polar factors.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectHSNorm_thresholdPolar_sub_intervalIntegrable (r : Nat)
    (X Y : Matrix ι κ ℂ) (a b : ℝ) :
    IntervalIntegrable (fun s => rectHSNorm r (matrixThresholdPolar X s - matrixThresholdPolar Y s) ^ 2)
      volume a b := by
  have hi := rectHSNorm_signedSpectral_sub_intervalIntegrable r
    (matrixSelfAdjointDilation_isHermitian X) (matrixSelfAdjointDilation_isHermitian Y) a b
  simp only [matrixSelfAdjointDilation_thresholdPolar, ← matrixSelfAdjointDilation_sub,
    rectHSNorm_selfAdjointDilation_sq] at hi
  convert hi.const_mul (1 / 2 : ℝ) using 1
  funext s
  ring

theorem rectHSNorm_one_dilation_le_two (r : Nat)
    (hdim : Fintype.card ι + Fintype.card κ ≤ 4 * r) :
    rectHSNorm r (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ≤ 2 := by
  have hs : rectHSNorm r (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ^ 2 ≤ 4 := by
    rw [rectHSNorm_one_sq, Fintype.card_sum]
    by_cases hr : r = 0
    · simp [hr]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr))).mpr
      exact_mod_cast hdim
  have hn := rectHSNorm_nonneg r (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
  nlinarith

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_selfAdjointDilation_le_two (r : Nat) (X : Matrix ι κ ℂ) :
    rectHSNorm r (matrixSelfAdjointDilation X) ≤ 2 * rectHSNorm r X := by
  have he := rectHSNorm_selfAdjointDilation_sq r X
  have hn := rectHSNorm_nonneg r (matrixSelfAdjointDilation X)
  have hm := rectHSNorm_nonneg r X
  nlinarith [sq_nonneg (rectHSNorm r X)]

theorem rectHSNorm_thresholdPolar_sub_coarea (r : Nat)
    (hdim : Fintype.card ι + Fintype.card κ ≤ 4 * r)
    (X Y : Matrix ι κ ℂ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, rectHSNorm r (matrixThresholdPolar X s - matrixThresholdPolar Y s) ^ 2) ≤
      4 * rectHSNorm r (X - Y) := by
  have he := rectHSNorm_signedSpectral_sub_coarea r
    (matrixSelfAdjointDilation_isHermitian X) (matrixSelfAdjointDilation_isHermitian Y) a b ha hab
  simp only [matrixSelfAdjointDilation_thresholdPolar, ← matrixSelfAdjointDilation_sub,
    rectHSNorm_selfAdjointDilation_sq, intervalIntegral.integral_const_mul] at he
  have hm := rectHSNorm_one_dilation_le_two r hdim
  have hn := rectHSNorm_selfAdjointDilation_le_two r (X - Y)
  have hbnd : 2 * rectHSNorm r (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *
      rectHSNorm r (matrixSelfAdjointDilation (X - Y)) ≤ 8 * rectHSNorm r (X - Y) := by
    calc
      _ ≤ (2 * 2) * (2 * rectHSNorm r (X - Y)) := mul_le_mul
        (mul_le_mul_of_nonneg_left hm (by norm_num)) hn (rectHSNorm_nonneg _ _) (by norm_num)
      _ = _ := by ring
  linarith

theorem rectHSNorm_thresholdPolar_intertwiner_intervalIntegrable (r : Nat)
    (V : Matrix.unitaryGroup ι ℂ) (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) (a b : ℝ) :
    IntervalIntegrable (fun s => rectHSNorm r
      (V.val * matrixThresholdPolar X s - matrixThresholdPolar X s * U.val) ^ 2) volume a b := by
  simp_rw [← matrixThresholdPolar_unitary_left, ← matrixThresholdPolar_unitary_right]
  exact rectHSNorm_thresholdPolar_sub_intervalIntegrable r _ _ a b

theorem rectHSNorm_thresholdPolar_intertwiner_coarea (r : Nat)
    (hdim : Fintype.card ι + Fintype.card κ ≤ 4 * r)
    (V : Matrix.unitaryGroup ι ℂ) (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, rectHSNorm r (V.val * matrixThresholdPolar X s - matrixThresholdPolar X s * U.val) ^ 2) ≤
      4 * rectHSNorm r (V.val * X - X * U.val) := by
  simp_rw [← matrixThresholdPolar_unitary_left, ← matrixThresholdPolar_unitary_right]
  exact rectHSNorm_thresholdPolar_sub_coarea r hdim _ _ a b ha hab

end ThomGame.Analysis
