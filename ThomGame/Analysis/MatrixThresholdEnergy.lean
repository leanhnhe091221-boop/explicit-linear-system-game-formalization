module

public import ThomGame.Analysis.MatrixThresholdPolarCoarea

/-!
# The integral energy estimate ALT (3.13)

Finite summation commutes with the actual threshold integral. A
weighted Cauchy--Schwarz bound uses the lazy Markov mass one quarter
and yields exactly the stated constant two.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {h : Nat}

theorem matrixIntertwiningEnergy_threshold_intervalIntegrable (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) (a b : ℝ) :
    IntervalIntegrable (fun s => matrixIntertwiningEnergy r U V (matrixThresholdPolar X s)) volume a b := by
  have hi := IntervalIntegrable.sum Finset.univ fun j _ =>
    rectHSNorm_thresholdPolar_intertwiner_intervalIntegrable r (V j) (U j) X a b
  have hs : IntervalIntegrable (fun s => ∑ j, rectHSNorm r
      ((V j).val * matrixThresholdPolar X s - matrixThresholdPolar X s * (U j).val) ^ 2) volume a b := by
    convert hi using 1
    funext s
    simp only [Finset.sum_apply]
  exact hs.const_mul (lazyMarkovWeight h)

theorem matrixIntertwiningEnergy_firstMoment_le [NeZero h] (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) :
    lazyMarkovWeight h * ∑ j, rectHSNorm r ((V j).val * X - X * (U j).val) ≤
      (1 / 2 : ℝ) * Real.sqrt (matrixIntertwiningEnergy r U V X) := by
  have he := weighted_abs_sum_sq_le (fun _ : Fin h => lazyMarkovWeight h)
    (fun j => rectHSNorm r ((V j).val * X - X * (U j).val)) (fun _ => lazyMarkovWeight_nonneg h)
  have hmass : (∑ _j : Fin h, lazyMarkovWeight h) = 1 / 4 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm, lazyMarkovWeight_mul_card]
  simp only [abs_of_nonneg (rectHSNorm_nonneg _ _), ← Finset.mul_sum] at he
  rw [hmass] at he
  have hI := matrixIntertwiningEnergy_nonneg r U V X
  have hroot := Real.sqrt_nonneg (matrixIntertwiningEnergy r U V X)
  have hsquare := Real.sq_sqrt hI
  change (lazyMarkovWeight h * ∑ j, rectHSNorm r ((V j).val * X - X * (U j).val)) ^ 2 ≤
    (1 / 4 : ℝ) * matrixIntertwiningEnergy r U V X at he
  nlinarith

theorem matrixThresholdPolar_energy_coarea [NeZero h] (r : Nat)
    (hdim : Fintype.card ι + Fintype.card κ ≤ 4 * r)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, matrixIntertwiningEnergy r U V (matrixThresholdPolar X s)) ≤
      2 * Real.sqrt (matrixIntertwiningEnergy r U V X) := by
  calc
    _ = lazyMarkovWeight h * ∑ j, ∫ s in a..b,
        rectHSNorm r ((V j).val * matrixThresholdPolar X s - matrixThresholdPolar X s * (U j).val) ^ 2 := by
      rw [show (fun s => matrixIntertwiningEnergy r U V (matrixThresholdPolar X s)) =
        (fun s => lazyMarkovWeight h * ∑ j, rectHSNorm r
          ((V j).val * matrixThresholdPolar X s - matrixThresholdPolar X s * (U j).val) ^ 2) from rfl,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      intro j _
      exact rectHSNorm_thresholdPolar_intertwiner_intervalIntegrable r (V j) (U j) X a b
    _ ≤ lazyMarkovWeight h * ∑ j, 4 * rectHSNorm r ((V j).val * X - X * (U j).val) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
        rectHSNorm_thresholdPolar_intertwiner_coarea r hdim (V j) (U j) X a b ha hab) (lazyMarkovWeight_nonneg h)
    _ = 4 * (lazyMarkovWeight h * ∑ j, rectHSNorm r ((V j).val * X - X * (U j).val)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (matrixIntertwiningEnergy_firstMoment_le r U V X) (by norm_num : (0 : ℝ) ≤ 4)
      linarith

theorem matrixThresholdPolar_ALT_3_13 [NeZero h]
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) (hdim : Fintype.card ι ≤ 3 * Fintype.card κ) :
    (∫ b in (0 : ℝ)..1, matrixIntertwiningEnergy (Fintype.card κ) U V (matrixThresholdPolar X b)) ≤
      2 * Real.sqrt (matrixIntertwiningEnergy (Fintype.card κ) U V X) :=
  matrixThresholdPolar_energy_coarea _ (by omega) U V X 0 1 le_rfl zero_le_one

end ThomGame.Analysis
