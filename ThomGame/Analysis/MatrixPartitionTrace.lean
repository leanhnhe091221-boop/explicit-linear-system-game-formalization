module

public import ThomGame.Analysis.MatrixPartitionAveraging

/-!
# Trace bounds for partition tilts

The trace of the actual range equals the trace of the original
initial projection. On the cube the parameter pairing is bounded
by this trace, keeping the original dimension as normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

omit [DecidableEq μ] in
theorem matrixPartitionRange_trace (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) {Y : Matrix ι κ ℂ}
    (hY : IsStarProjection (Yᴴ * Y)) (t : ℝ) (s : μ → ℝ) :
    matrixTraceReal r (matrixPartitionRange E Y t s) = matrixTraceReal r (Yᴴ * Y) := by
  change matrixTraceReal r (matrixExponentialPolarTilt t (matrixProjectionParameter E s) Y *
    (matrixExponentialPolarTilt t (matrixProjectionParameter E s) Y)ᴴ) = _
  rw [matrixTraceReal_mul_comm,
    matrixExponentialPolarTilt_initial t (matrixProjectionParameter_isHermitian E hE s) hY]

omit [Fintype κ] [DecidableEq κ] [DecidableEq μ] in
theorem matrixProjectionParameter_trace_le (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (hsum : ∑ i, E i = 1)
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (s : μ → ℝ) (hs : ∀ i, s i ≤ 1) :
    matrixTraceReal r (matrixProjectionParameter E s * P) ≤ matrixTraceReal r P := by
  calc
    _ = ∑ i, s i * matrixTraceReal r (E i * P) := by
      simp only [matrixProjectionParameter, Matrix.sum_mul, Matrix.smul_mul,
        matrixTraceReal_sum, matrixTraceReal_real_smul]
    _ ≤ ∑ i, matrixTraceReal r (E i * P) :=
      Finset.sum_le_sum fun i _ => mul_le_of_le_one_left
        (matrixTraceReal_projection_product_nonneg r (hE i) hP) (hs i)
    _ = _ := by rw [← matrixTraceReal_sum, ← Matrix.sum_mul, hsum, Matrix.one_mul]

omit [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ] in
theorem matrixTraceReal_projection_le_one {P : Matrix κ κ ℂ} (hP : IsStarProjection P) :
    matrixTraceReal (Fintype.card κ) P ≤ 1 := by
  have he := matrixTraceReal_mono (Fintype.card κ) hP.le_one
  have ht : matrixTraceReal (Fintype.card κ) (1 : Matrix κ κ ℂ) ≤ 1 := by
    simp only [matrixTraceReal, Matrix.trace_one, Complex.natCast_re]
    exact div_self_le_one (Fintype.card κ : ℝ)
  exact he.trans ht

theorem matrixPartitionRange_weighted_expectation_le_one (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) (t : ℝ) :
    t * (∫ s, ∑ j, (1 - (s j) ^ 2) * matrixProjectionMixing (Fintype.card κ) (E j)
      (matrixPartitionRange E Y t s) ∂uniformCubeMeasure) ≤ 1 := by
  rw [matrixPartitionRange_joint_expectation _ E hE horth Y t]
  have hP := matrixPartitionRange_continuous E hE Y t
  have hA := matrixProjectionParameter_continuous E
  have hc : Continuous (fun s => matrixTraceReal (Fintype.card κ)
      (matrixProjectionParameter E s * matrixPartitionRange E Y t s)) :=
    (matrixTraceRealCLM _).continuous.comp (hA.matrix_mul hP)
  calc
    _ ≤ ∫ _ : μ → ℝ, matrixTraceReal (Fintype.card κ) (Yᴴ * Y) ∂uniformCubeMeasure := by
      apply integral_mono_ae (uniformCube_integrable hc) (integrable_const _)
      filter_upwards [uniformCubeMeasure_ae] with s hs
      exact (matrixProjectionParameter_trace_le _ E hE hsum
        (matrixPartitionRange_isStarProjection E Y t s) s
        (fun i => (le_abs_self (s i)).trans (mem_uniformCube.mp hs i))).trans_eq
        (matrixPartitionRange_trace _ E hE hY t s)
    _ ≤ 1 := by simpa using matrixTraceReal_projection_le_one hY

end ThomGame.Analysis
