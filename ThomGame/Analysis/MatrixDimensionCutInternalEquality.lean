module

public import ThomGame.Analysis.MatrixDimensionCutLimits
public import ThomGame.Analysis.MatrixThomStableInternalEquality

/-!
# The cut and scalar extension preserve the original internal algebra

The original ambient quotient is unchanged here. Both directions are
proved from actual uniform coordinate approximations with the original
dimension in the Hilbert--Schmidt norm. Moving the retained support to
the specified standard target corner is a separate step.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixDimensionCut_nearInclusions {m d : Nat} {A : StarSubalgebra ℂ (CMatrix m)}
    (S : MatrixSubalgebraDimensionCut A d) :
    MatrixNearInclusion A (matrixDimensionCutLiftedAlgebra S)
        (2 * Real.sqrt (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ))) ∧
      MatrixNearInclusion (matrixDimensionCutLiftedAlgebra S) A
        (2 * Real.sqrt (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ))) := by
  constructor
  · intro X hX hn
    obtain ⟨Y, hY, _, he⟩ := matrixDimensionCut_forward_approximation S m X hX hn
    rw [rectHSNorm_eq_hsNorm] at he
    exact ⟨Y, hY, by linarith [Real.sqrt_nonneg (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ))]⟩
  · intro Y hY hn
    obtain ⟨X, hX, _, he⟩ := matrixDimensionCut_reverse_approximation S m Y hY hn
    exact ⟨X, hX, by simpa only [rectHSNorm_eq_hsNorm] using he⟩

theorem matrixDimensionCut_internal_eq {ι : Type*}
    (source target : ι → Nat) [∀ i, NeZero (source i)]
    {A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i))}
    (S : (i : ι) → MatrixSubalgebraDimensionCut (A i) (target i))
    (hd : ∀ i, target i ≤ source i) (L : Filter ι)
    (hratio : Filter.Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    matrixInternalQuotient source A L =
      matrixInternalQuotient source (fun i => matrixDimensionCutLiftedAlgebra (S i)) L := by
  apply matrixInternal_eq_of_mutual_nearInclusion_errors source _ _ L
    (fun i => 2 * Real.sqrt (2 * matrixTraceReal (source i) (1 - (S i).frame * (S i).frameᴴ)))
  · simpa using (((matrixDimensionCut_complement_trace_tendsto source target S hd hratio).const_mul 2).sqrt).const_mul 2
  · exact fun i => (matrixDimensionCut_nearInclusions (S i)).1
  · exact fun i => (matrixDimensionCut_nearInclusions (S i)).2

end ThomGame.Analysis
