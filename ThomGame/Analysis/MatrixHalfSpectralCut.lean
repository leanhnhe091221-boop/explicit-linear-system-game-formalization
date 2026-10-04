module

public import ThomGame.Analysis.MatrixPartitionGoodParameter

/-!
# The closed half spectral cut of a positive matrix contraction

Scalar rounding inequalities are transported by the actual finite
spectral calculus. The endpoint one half belongs to the upper cut.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem half_step_abs_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |spectralStep (1 / 2) x - x| ≤ 2 * (x - x * x) := by
  by_cases hx : (1 / 2 : ℝ) ≤ x
  · simp only [spectralStep, ite_eq_left hx, abs_of_nonneg (sub_nonneg.mpr hx1)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * x - 1) (sub_nonneg.mpr hx1)]
  · simp only [spectralStep, ite_eq_right hx, zero_sub, abs_neg, abs_of_nonneg hx0]
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]

theorem half_step_distance_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x + spectralStep (1 / 2) x - 2 * (x * spectralStep (1 / 2) x) ≤
      2 * (x - x * x) := by
  have he := half_step_abs_error hx0 hx1
  by_cases hx : (1 / 2 : ℝ) ≤ x
  · simp only [spectralStep, ite_eq_left hx, abs_of_nonneg (sub_nonneg.mpr hx1)] at he ⊢
    linarith
  · simp only [spectralStep, ite_eq_right hx, zero_sub, abs_neg, abs_of_nonneg hx0] at he ⊢
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixHalfProjection (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (spectralStep (1 / 2)) A

theorem matrixHalfProjection_isStarProjection (A : Matrix ι ι ℂ) :
    IsStarProjection (matrixHalfProjection A) := by
  constructor
  · show matrixHalfProjection A * matrixHalfProjection A = matrixHalfProjection A
    rw [matrixHalfProjection, ← cfc_mul _ _ A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x _
    exact (pow_two _).symm.trans (spectralStep_sq _ _)
  · exact IsSelfAdjoint.cfc

theorem matrixHalfProjection_commute {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    {X : Matrix ι ι ℂ} (hX : Commute X A) : Commute X (matrixHalfProjection A) := by
  show X * matrixHalfProjection A = matrixHalfProjection A * X
  exact (matrix_cfc_intertwine hA hA (spectralStep (1 / 2)) X hX.eq.symm).symm

theorem matrixHalfProjection_eq_closed_interval {A : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hA1 : A ≤ 1) :
    matrixHalfProjection A = cfc (fun x : ℝ => if 1 / 2 ≤ x ∧ x ≤ 1 then 1 else 0) A := by
  unfold matrixHalfProjection
  apply cfc_congr
  intro x hx
  have hx1 := (CFC.le_one_iff (R := ℝ) A hA.isSelfAdjoint).mp hA1 x hx
  simp only [spectralStep, hx1, and_true]

theorem matrix_cfc_variance {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    cfc (fun x : ℝ => x - x * x) A = A - A * A := by
  rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  rw [hid]

theorem matrixHalfProjection_order_bounds {A : Matrix ι ι ℂ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    matrixHalfProjection A - A ≤ (2 : ℝ) • (A - A * A) ∧
      A - matrixHalfProjection A ≤ (2 : ℝ) • (A - A * A) ∧
      A + matrixHalfProjection A - (2 : ℝ) • (A * matrixHalfProjection A) ≤
        (2 : ℝ) • (A - A * A) := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA0.isSelfAdjoint
  have hc : cfc (fun x : ℝ => 2 * (x - x * x)) A = (2 : ℝ) • (A - A * A) := by
    rw [cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _), matrix_cfc_variance hA0.isSelfAdjoint.isHermitian]
  have he : cfc (fun x : ℝ => spectralStep (1 / 2) x - x) A = matrixHalfProjection A - A := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hid]
    rfl
  have hf : cfc (fun x : ℝ => x - spectralStep (1 / 2) x) A = A - matrixHalfProjection A := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hid]
    rfl
  have hg : cfc (fun x : ℝ => x + spectralStep (1 / 2) x - 2 * (x * spectralStep (1 / 2) x)) A =
      A + matrixHalfProjection A - (2 : ℝ) • (A * matrixHalfProjection A) := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_add A _ _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _),
      cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hid]
    rfl
  have hb (x : ℝ) (hx : x ∈ spectrum ℝ A) : 0 ≤ x ∧ x ≤ 1 :=
    ⟨spectrum_nonneg_of_nonneg hA0 hx, (CFC.le_one_iff (R := ℝ) A hA0.isSelfAdjoint).mp hA1 x hx⟩
  rw [← hc, ← he, ← hf, ← hg]
  refine ⟨?_, ?_, ?_⟩
  · apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
    intro x hx
    exact (le_abs_self _).trans (half_step_abs_error (hb x hx).1 (hb x hx).2)
  · apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
    intro x hx
    have he := (neg_le_abs (spectralStep (1 / 2) x - x)).trans (half_step_abs_error (hb x hx).1 (hb x hx).2)
    simpa only [neg_sub] using he
  · apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
    intro x hx
    exact half_step_distance_error (hb x hx).1 (hb x hx).2

end ThomGame.Analysis
