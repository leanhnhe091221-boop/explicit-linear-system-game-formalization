module

public import ThomGame.Analysis.MatrixRangeContinuity
public import ThomGame.Analysis.UniformCube
public import ThomGame.Analysis.ProductResampling

/-!
# Joint averaging of the actual exponential range

Coordinate integration by parts is integrated against the independent
uniform parameters. All integrability follows from joint continuity
on the compact cube.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

omit [DecidableEq μ] in
theorem matrixPartitionRange_mixing_continuous (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (Y : Matrix ι κ ℂ) (t : ℝ) (j : μ) :
    Continuous (fun s => matrixProjectionMixing r (E j) (matrixPartitionRange E Y t s)) :=
  (matrixProjectionMixing_continuous r (E j)).comp (matrixPartitionRange_continuous E hE Y t)

omit [DecidableEq μ] in
theorem matrixPartitionRange_trace_continuous (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (Y : Matrix ι κ ℂ) (t : ℝ) (j : μ) :
    Continuous (fun s => matrixTraceReal r (E j * matrixPartitionRange E Y t s)) :=
  (matrixTraceRealCLM r).continuous.comp
    (continuous_const.matrix_mul (matrixPartitionRange_continuous E hE Y t))

theorem matrixPartitionRange_coordinate_expectation (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (Y : Matrix ι κ ℂ) (t : ℝ) (j : μ) :
    t * (∫ s, (1 - (s j) ^ 2) * matrixProjectionMixing r (E j)
      (matrixPartitionRange E Y t s) ∂uniformCubeMeasure) =
    ∫ s, s j * matrixTraceReal r (E j * matrixPartitionRange E Y t s) ∂uniformCubeMeasure := by
  have hm := matrixPartitionRange_mixing_continuous r E hE Y t j
  have hp := matrixPartitionRange_trace_continuous r E hE Y t j
  have hi : Integrable (fun s => (1 - (s j) ^ 2) * matrixProjectionMixing r (E j)
      (matrixPartitionRange E Y t s)) uniformCubeMeasure := uniformCube_integrable (by fun_prop)
  have hj : Integrable (fun s => s j * matrixTraceReal r (E j * matrixPartitionRange E Y t s))
      uniformCubeMeasure := uniformCube_integrable (by fun_prop)
  dsimp only [uniformCubeMeasure] at hi hj ⊢
  rw [← integral_product_update uniformIntervalMeasure j hi,
    ← integral_product_update uniformIntervalMeasure j hj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Function.update_self, uniformIntervalMeasure_integral]
  have he := matrixPartitionRange_coordinate_interval r E hE horth Y t s j
  linarith

theorem matrixPartitionRange_joint_expectation (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (Y : Matrix ι κ ℂ) (t : ℝ) :
    t * (∫ s, ∑ j, (1 - (s j) ^ 2) * matrixProjectionMixing r (E j)
      (matrixPartitionRange E Y t s) ∂uniformCubeMeasure) =
    ∫ s, matrixTraceReal r (matrixProjectionParameter E s * matrixPartitionRange E Y t s)
      ∂uniformCubeMeasure := by
  have hm (j : μ) := matrixPartitionRange_mixing_continuous r E hE Y t j
  have hp (j : μ) := matrixPartitionRange_trace_continuous r E hE Y t j
  have hi (j : μ) : Integrable (fun s => (1 - (s j) ^ 2) * matrixProjectionMixing r (E j)
      (matrixPartitionRange E Y t s)) uniformCubeMeasure := uniformCube_integrable (by fun_prop)
  have hj (j : μ) : Integrable (fun s => s j * matrixTraceReal r (E j * matrixPartitionRange E Y t s))
      uniformCubeMeasure := uniformCube_integrable (by fun_prop)
  simp_rw [matrixProjectionParameter, Matrix.sum_mul, Matrix.smul_mul,
    matrixTraceReal_sum, matrixTraceReal_real_smul]
  rw [integral_finsetSum _ (fun j _ => hi j), Finset.mul_sum,
    integral_finsetSum _ (fun j _ => hj j)]
  exact Finset.sum_congr rfl (fun j _ => matrixPartitionRange_coordinate_expectation r E hE horth Y t j)

end ThomGame.Analysis
