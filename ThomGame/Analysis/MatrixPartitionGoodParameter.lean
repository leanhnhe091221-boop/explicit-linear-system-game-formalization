module

public import ThomGame.Analysis.MatrixPartitionTrace
public import ThomGame.Analysis.UniformMixingSelection

/-!
# An actual small-defect parameter in ALT Lemma 3.4

For dim K <= 3 dim H, the actual exponential range has expected
pinching defect at most (t epsilon)^(-1)+3 epsilon. Choosing
epsilon=t^(-1/2) produces a point in the cube with defect at most
4 t^(-1/2), with no averaging or selection premise remaining.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

omit [DecidableEq κ] [DecidableEq μ] in
theorem matrixPartition_trace_sum_le_three (E : μ → Matrix ι ι ℂ)
    (hsum : ∑ i, E i = 1) (hdim : Fintype.card ι ≤ 3 * Fintype.card κ) :
    (∑ i, matrixTraceReal (Fintype.card κ) (E i)) ≤ 3 := by
  rw [← matrixTraceReal_sum, hsum, matrixTraceReal, Matrix.trace_one, Complex.natCast_re]
  by_cases hr : Fintype.card κ = 0
  · simp [hr]
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr))).mpr
    exact_mod_cast hdim

theorem matrixPartitionRange_defect_expectation_le (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) (hdim : Fintype.card ι ≤ 3 * Fintype.card κ)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s, rectHSNorm (Fintype.card κ) (matrixPartitionRange E Y t s -
      matrixBlockPinch E (matrixPartitionRange E Y t s)) ^ 2 ∂uniformCubeMeasure) ≤
      (t * ε)⁻¹ + 3 * ε := by
  simp_rw [matrixPartitionRange_defect _ E hE horth hsum Y t]
  have he := uniformCube_mixing_expectation_le
    (fun j s => matrixProjectionMixing (Fintype.card κ) (E j) (matrixPartitionRange E Y t s))
    (fun j => matrixTraceReal (Fintype.card κ) (E j))
    (matrixPartitionRange_mixing_continuous _ E hE Y t)
    (fun s _ j => matrixProjectionMixing_nonneg _ (hE j) (matrixPartitionRange_isStarProjection E Y t s))
    (fun s _ j => matrixProjectionMixing_le_trace _ (hE j) (matrixPartitionRange_isStarProjection E Y t s))
    ht hε hε1 (matrixPartitionRange_weighted_expectation_le_one E hE horth hsum hY t)
  exact he.trans (add_le_add le_rfl (by
    simpa only [mul_comm ε 3] using mul_le_mul_of_nonneg_left
      (matrixPartition_trace_sum_le_three E hsum hdim) hε.le))

theorem exists_matrixPartitionRange_small_defect (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) (hdim : Fintype.card ι ≤ 3 * Fintype.card κ)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) {t : ℝ} (ht : 1 ≤ t) :
    ∃ s : μ → ℝ, (∀ i, |s i| ≤ 1) ∧
      rectHSNorm (Fintype.card κ) (matrixPartitionRange E Y t s -
        matrixBlockPinch E (matrixPartitionRange E Y t s)) ^ 2 ≤ 4 * (Real.sqrt t)⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hε : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hroot
  have hε1 : (Real.sqrt t)⁻¹ ≤ 1 := (inv_le_one₀ hroot).mpr (Real.one_le_sqrt.mpr ht)
  have hparam : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    calc
      _ = (Real.sqrt t * Real.sqrt t) * (Real.sqrt t)⁻¹ := by rw [Real.mul_self_sqrt ht0.le]
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hroot.ne', mul_one]
  have hb := matrixPartitionRange_defect_expectation_le E hE horth hsum hdim hY ht0 hε hε1
  rw [hparam] at hb
  have hc : Continuous (fun s => ∑ j, matrixProjectionMixing (Fintype.card κ) (E j)
      (matrixPartitionRange E Y t s)) := by
    exact continuous_finsetSum _ (fun j _ => matrixPartitionRange_mixing_continuous _ E hE Y t j)
  obtain ⟨s, hs, hgood⟩ := uniformCube_exists_le_integral hc
  refine ⟨s, mem_uniformCube.mp hs, ?_⟩
  simp_rw [matrixPartitionRange_defect _ E hE horth hsum Y t] at hb ⊢
  linarith

theorem exists_matrixPartitionPolarTilt_good_parameter {h : Nat}
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (hsum : ∑ i, E i = 1)
    (hdim : Fintype.card ι ≤ 3 * Fintype.card κ)
    (hcomm : ∀ j i, (V j).val * E i = E i * (V j).val)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) {t : ℝ} (ht : 1 ≤ t) :
    ∃ s : μ → ℝ, (∀ i, |s i| ≤ 1) ∧
      let YA := matrixExponentialPolarTilt t (matrixProjectionParameter E s) Y
      YAᴴ * YA = Yᴴ * Y ∧
      rectHSNorm (Fintype.card κ) (YA * YAᴴ - matrixBlockPinch E (YA * YAᴴ)) ^ 2 ≤
        4 * (Real.sqrt t)⁻¹ ∧
      matrixIntertwiningEnergy (Fintype.card κ) U V YA ≤
        Real.exp (4 * t) * matrixIntertwiningEnergy (Fintype.card κ) U V Y := by
  obtain ⟨s, hs, hgood⟩ := exists_matrixPartitionRange_small_defect E hE horth hsum hdim hY ht
  refine ⟨s, hs, matrixExponentialPolarTilt_initial t
    (matrixProjectionParameter_isHermitian E hE s) hY, hgood, ?_⟩
  exact matrixPartitionPolarTilt_energy _ U V E hE horth hsum hcomm hY
    (zero_le_one.trans ht) s hs

end ThomGame.Analysis
