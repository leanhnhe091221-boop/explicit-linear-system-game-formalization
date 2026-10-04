module

public import ThomGame.Analysis.MatrixProjectionParameters

/-!
# Exponential ranges for the actual projection-partition parameters

This instantiates the energy, derivative, mixing, and interval
identities with A(s)=sum s_i E_i. All commuting-direction hypotheses
are proved from the given orthogonal projection partition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

noncomputable def matrixPartitionRange (E : μ → Matrix ι ι ℂ) (Y : Matrix ι κ ℂ)
    (t : ℝ) (s : μ → ℝ) : Matrix ι ι ℂ :=
  matrixExponentialRange t (matrixProjectionParameter E s) Y

omit [DecidableEq μ] in
theorem matrixPartitionRange_isStarProjection (E : μ → Matrix ι ι ℂ) (Y : Matrix ι κ ℂ)
    (t : ℝ) (s : μ → ℝ) : IsStarProjection (matrixPartitionRange E Y t s) :=
  matrixExponentialRange_isStarProjection _ _ _

theorem matrixPartitionRange_coordinate_derivative (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (Y : Matrix ι κ ℂ) (t : ℝ) (s : μ → ℝ) (j : μ) :
    HasDerivAt (fun a => matrixPartitionRange E Y t (Function.update s j a))
      (t • ((1 - matrixPartitionRange E Y t s) * E j * matrixPartitionRange E Y t s +
        matrixPartitionRange E Y t s * E j * (1 - matrixPartitionRange E Y t s))) (s j) := by
  have he := matrixExponentialRange_hasDerivAt
    (matrixProjectionParameter_isHermitian E hE (Function.update s j 0))
    (hE j).isSelfAdjoint.isHermitian (matrixProjectionParameter_commute E hE horth (Function.update s j 0) j)
    Y t (s j)
  simpa only [← matrixProjectionParameter_update E s j, Function.update_eq_self, matrixPartitionRange] using! he

theorem matrixPartitionRange_trace_derivative (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (Y : Matrix ι κ ℂ) (t : ℝ) (s : μ → ℝ) (j : μ) :
    HasDerivAt (fun a => matrixTraceReal r (E j * matrixPartitionRange E Y t (Function.update s j a)))
      (2 * t * matrixProjectionMixing r (E j) (matrixPartitionRange E Y t s)) (s j) := by
  have he := matrixExponentialRange_trace_hasDerivAt r
    (matrixProjectionParameter_isHermitian E hE (Function.update s j 0)) (hE j)
    (matrixProjectionParameter_commute E hE horth (Function.update s j 0) j) Y t (s j)
  simpa only [← matrixProjectionParameter_update E s j, Function.update_eq_self, matrixPartitionRange] using! he

theorem matrixPartitionRange_coordinate_interval (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (Y : Matrix ι κ ℂ) (t : ℝ) (s : μ → ℝ) (j : μ) :
    t * (∫ a in (-1 : ℝ)..1, (1 - a ^ 2) *
      matrixProjectionMixing r (E j) (matrixPartitionRange E Y t (Function.update s j a))) =
    ∫ a in (-1 : ℝ)..1, a * matrixTraceReal r (E j * matrixPartitionRange E Y t (Function.update s j a)) := by
  have he := matrixExponentialMixing_interval_identity r
    (matrixProjectionParameter_isHermitian E hE (Function.update s j 0)) (hE j)
    (matrixProjectionParameter_commute E hE horth (Function.update s j 0) j) Y t
  simpa only [← matrixProjectionParameter_update E s j, matrixPartitionRange] using he

omit [DecidableEq μ] in
theorem matrixPartitionRange_defect (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) (Y : Matrix ι κ ℂ) (t : ℝ) (s : μ → ℝ) :
    rectHSNorm r (matrixPartitionRange E Y t s - matrixBlockPinch E (matrixPartitionRange E Y t s)) ^ 2 =
      ∑ i, matrixProjectionMixing r (E i) (matrixPartitionRange E Y t s) :=
  rectHSNorm_pinching_defect_eq_mixing_sum r E hE horth hsum (matrixPartitionRange_isStarProjection E Y t s)

omit [DecidableEq μ] in
theorem matrixPartitionPolarTilt_energy {h : Nat} (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (hsum : ∑ i, E i = 1)
    (hcomm : ∀ j i, (V j).val * E i = E i * (V j).val)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) {t : ℝ} (ht : 0 ≤ t)
    (s : μ → ℝ) (hs : ∀ i, |s i| ≤ 1) :
    matrixIntertwiningEnergy r U V (matrixExponentialPolarTilt t (matrixProjectionParameter E s) Y) ≤
      Real.exp (4 * t) * matrixIntertwiningEnergy r U V Y :=
  matrixExponentialPolarTilt_energy_le r U V (matrixProjectionParameter_isHermitian E hE s)
    (matrixProjectionParameter_norm_le_one E hE horth hsum s hs) hY ht
    (fun j => matrixProjectionParameter_commute_of_blocks E s (V j).val (hcomm j))

end ThomGame.Analysis
