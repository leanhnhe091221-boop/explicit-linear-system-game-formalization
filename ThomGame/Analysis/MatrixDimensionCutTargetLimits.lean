module

public import ThomGame.Analysis.MatrixDimensionCutTargetHausdorff
public import ThomGame.Analysis.MatrixDimensionCutInternalEquality
public import ThomGame.Analysis.MatrixFrameInternalEquivalence

/-!
# Equality under the canonical corner map for decreasing dimensions

The target algebras lie in the prescribed dimensions, and their images
under the standard coordinate corner map equal the original internal algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (source target : ι → Nat) [∀ i, NeZero (source i)]
    {A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i))}
    (S : (i : ι) → MatrixSubalgebraDimensionCut (A i) (target i))
    (hd : ∀ i, target i ≤ source i) (T : (i : ι) → MatrixDimensionCutTarget (S i) (hd i))
    {L : Filter ι}

include hd in
theorem matrixDimensionCutTarget_error_tendsto
    (hratio : Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    Tendsto (fun i => 2 * Real.sqrt (2 * matrixTraceReal (source i) (1 - (S i).frame * (S i).frameᴴ)) +
      8 * Real.sqrt (matrixTraceReal (source i) (1 - (S i).frame * (S i).frameᴴ))) L (𝓝 0) := by
  have ht := matrixDimensionCut_complement_trace_tendsto source target S hd hratio
  simpa using (((ht.const_mul 2).sqrt).const_mul 2).add (ht.sqrt.const_mul 8)

theorem matrixDimensionCutTarget_hausdorff_tendsto
    (hratio : Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    Tendsto (fun i => matrixHSUnitBallHausdorff (source i) (A i) (T i).liftedAlgebra) L (𝓝 0) := by
  exact squeeze_zero (fun i => matrixHSUnitBallHausdorff_nonneg _ _ _)
    (fun i => (T i).hausdorff_bound) (matrixDimensionCutTarget_error_tendsto source target S hd hratio)

theorem matrixDimensionCutTarget_internal_eq
    (hratio : Tendsto (fun i => (target i : ℝ) / source i) L (𝓝 1)) :
    matrixInternalQuotient source A L = matrixInternalQuotient source (fun i => (T i).liftedAlgebra) L := by
  apply matrixInternal_eq_of_mutual_nearInclusion_errors source _ _ L _
    (matrixDimensionCutTarget_error_tendsto source target S hd hratio)
  · intro i X hX hn
    obtain ⟨Y, hY, _, he⟩ := (T i).unitBall_approximations.1 X hX hn
    exact ⟨Y, hY, by simpa only [rectHSNorm_eq_hsNorm] using he⟩
  · intro i Y hY hn
    obtain ⟨X, hX, _, he⟩ := (T i).unitBall_approximations.2 Y hY hn
    exact ⟨X, hX, by simpa only [rectHSNorm_eq_hsNorm] using he⟩

theorem matrixDimensionCutTarget_canonical_map (hpos : ∀ i, 0 < target i)
    (hratio : Tendsto (fun i => (source i : ℝ) / target i) L (𝓝 1)) :
    (matrixInternalQuotient target (fun i => (T i).algebra) L).map
      (matrixFrameQuotientHom target source (fun i => matrixCanonicalCornerFrame (hd i))
        (fun i => matrixCanonicalCornerFrame_initial (hd i)) hpos (fun i => NeZero.pos (source i)) L hratio) =
      matrixInternalQuotient source A L := by
  rw [matrixFrameQuotientHom_internal_map]
  exact (matrixDimensionCutTarget_internal_eq source target S hd T
    (matrixDimensionRatio_inverse_tendsto target source L hratio)).symm

theorem exists_matrixDimensionDecreasing_canonical_algebras
    (A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i)))
    (hpos : ∀ i, 0 < target i)
    (hratio : Tendsto (fun i => (source i : ℝ) / target i) L (𝓝 1)) :
    ∃ B : (i : ι) → StarSubalgebra ℂ (CMatrix (target i)),
      (matrixInternalQuotient target B L).map
        (matrixFrameQuotientHom target source (fun i => matrixCanonicalCornerFrame (hd i))
          (fun i => matrixCanonicalCornerFrame_initial (hd i)) hpos (fun i => NeZero.pos (source i)) L hratio) =
        matrixInternalQuotient source A L := by
  classical
  let S' : (i : ι) → MatrixSubalgebraDimensionCut (A i) (target i) :=
    fun i => (exists_matrixSubalgebraDimensionCut (A i) (target i) (hd i)).some
  let T' : (i : ι) → MatrixDimensionCutTarget (S' i) (hd i) :=
    fun i => (exists_matrixDimensionCutTarget (S' i) (hd i)).some
  exact ⟨fun i => (T' i).algebra, matrixDimensionCutTarget_canonical_map source target S' hd T' hpos hratio⟩

end ThomGame.Analysis
