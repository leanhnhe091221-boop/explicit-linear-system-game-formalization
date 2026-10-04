module

public import ThomGame.Analysis.MatrixDimensionCutHausdorff

/-!
# Vanishing cut losses under a relative dimension change

The bound e^2 <= (m-d)m gives e/m <= sqrt(1-d/m). It covers bounded
and unbounded dimensions uniformly and yields vanishing support loss and
unit-ball Hausdorff distance in the original dimension normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixDimensionCut_slack_ratio_bound {m d : Nat} [NeZero m]
    {A : StarSubalgebra ℂ (CMatrix m)} (S : MatrixSubalgebraDimensionCut A d) (hd : d ≤ m) :
    (S.slack : ℝ) / m ≤ Real.sqrt (1 - (d : ℝ) / m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have he : (S.slack : ℝ) ^ 2 ≤ ((m - d : Nat) : ℝ) * m := by exact_mod_cast S.slack_sq_le
  rw [Nat.cast_sub hd] at he
  have hsq : ((S.slack : ℝ) / m) ^ 2 ≤ 1 - (d : ℝ) / m := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    calc
      _ ≤ ((m : ℝ) - d) * m := he
      _ = _ := by field_simp
  simpa only [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hm.le)] using Real.sqrt_le_sqrt hsq

variable {ι : Type*} (source target : ι → Nat) [∀ i, NeZero (source i)]
    {A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i))}
    (S : (i : ι) → MatrixSubalgebraDimensionCut (A i) (target i))
    (hd : ∀ i, target i ≤ source i) {L : Filter ι}

include hd in
theorem matrixDimensionCut_slack_ratio_tendsto
    (hratio : Filter.Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    Filter.Tendsto (fun i => ((S i).slack : ℝ) / source i) L (𝓝 0) := by
  have h1 : Filter.Tendsto (fun _ : ι => (1 : ℝ)) L (𝓝 1) := tendsto_const_nhds
  apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun i => matrixDimensionCut_slack_ratio_bound (S i) (hd i))
  simpa using (h1.sub hratio).sqrt

include hd in
theorem matrixDimensionCut_complement_trace_tendsto
    (hratio : Filter.Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    Filter.Tendsto (fun i => matrixTraceReal (source i) (1 - (S i).frame * (S i).frameᴴ)) L (𝓝 0) := by
  have h1 : Filter.Tendsto (fun _ : ι => (1 : ℝ)) L (𝓝 1) := tendsto_const_nhds
  have ht := (h1.sub hratio).add (matrixDimensionCut_slack_ratio_tendsto source target S hd hratio)
  simp only [sub_self, zero_add] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro i
  change 1 - (target i : ℝ) / source i + ((S i).slack : ℝ) / source i =
    matrixTraceReal (source i) (1 - (S i).frame * (S i).frameᴴ)
  rw [matrixSubalgebraDimensionCut_complement_trace (A i) (target i) (S i) (hd i),
    Nat.cast_sub (hd i), add_div, sub_div, div_self (by exact_mod_cast NeZero.ne (source i))]

include hd in
theorem matrixDimensionCut_hausdorff_tendsto
    (hratio : Filter.Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    Filter.Tendsto (fun i => matrixHSUnitBallHausdorff (source i) (A i) (matrixDimensionCutLiftedAlgebra (S i)))
      L (𝓝 0) := by
  apply squeeze_zero (fun i => matrixHSUnitBallHausdorff_nonneg _ _ _)
    (fun i => matrixDimensionCut_hausdorff_bound (S i) (source i))
  simpa using (((matrixDimensionCut_complement_trace_tendsto source target S hd hratio).const_mul 2).sqrt).const_mul 2

end ThomGame.Analysis
