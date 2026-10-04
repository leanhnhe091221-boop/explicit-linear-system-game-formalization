module

public import ThomGame.Analysis.MatrixCanonicalDimensionEquivalence
public import ThomGame.Analysis.MatrixDimensionCutTargetLimits
public import ThomGame.Analysis.MatrixUnitBallHausdorffRescale

/-!
# Thom Lemma 2.3: canonical stability under negligible dimension changes

The algebras in the specified target dimensions are constructed from
actual block cuts. Both standard corner extensions are compared in the
common coordinate space, with the original source normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def matrixCanonicalSourceAlgebra {m d : Nat} (A : StarSubalgebra ℂ (CMatrix m)) :
    StarSubalgebra ℂ (CMatrix (max m d)) :=
  matrixFrameScalarAlgebra A (matrixCanonicalCornerFrame (Nat.le_max_left m d))
    (matrixCanonicalCornerFrame_initial (Nat.le_max_left m d))

noncomputable def matrixCanonicalTargetAlgebra {m d : Nat} (B : StarSubalgebra ℂ (CMatrix d)) :
    StarSubalgebra ℂ (CMatrix (max m d)) :=
  matrixFrameScalarAlgebra B (matrixCanonicalCornerFrame (Nat.le_max_right m d))
    (matrixCanonicalCornerFrame_initial (Nat.le_max_right m d))

theorem exists_matrixCanonicalDimensionStability {ι : Type*} (source target : ι → Nat)
    [∀ i, NeZero (source i)] (ht : ∀ i, 0 < target i)
    (L : Filter ι) (hratio : Tendsto (fun i => (source i : ℝ) / target i) L (𝓝 1))
    (A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i))) :
    ∃ B : (i : ι) → StarSubalgebra ℂ (CMatrix (target i)),
      (matrixInternalQuotient source A L).map
        (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom =
        matrixInternalQuotient target B L ∧
      Tendsto (fun i => matrixHSUnitBallHausdorff (source i)
        (matrixCanonicalSourceAlgebra (d := target i) (A i))
        (matrixCanonicalTargetAlgebra (m := source i) (B i))) L (𝓝 0) := by
  classical
  let N : ι → Nat := fun i => max (source i) (target i)
  let hN : ∀ i, 0 < N i := fun i => (NeZero.pos (source i)).trans_le (Nat.le_max_left _ _)
  let : ∀ i, NeZero (N i) := fun i => ⟨Nat.ne_of_gt (hN i)⟩
  let A' : (i : ι) → StarSubalgebra ℂ (CMatrix (N i)) :=
    fun i => matrixCanonicalSourceAlgebra (d := target i) (A i)
  let hd : ∀ i, target i ≤ N i := fun i => Nat.le_max_right _ _
  let S : (i : ι) → MatrixSubalgebraDimensionCut (A' i) (target i) :=
    fun i => (exists_matrixSubalgebraDimensionCut (A' i) (target i) (hd i)).some
  let T : (i : ι) → MatrixDimensionCutTarget (S i) (hd i) :=
    fun i => (exists_matrixDimensionCutTarget (S i) (hd i)).some
  let B : (i : ι) → StarSubalgebra ℂ (CMatrix (target i)) := fun i => (T i).algebra
  have hrN : Tendsto (fun i => (N i : ℝ) / target i) L (𝓝 1) :=
    matrixDimensionRatio_max_target_tendsto source target ht L hratio
  have hrS : Tendsto (fun i => (N i : ℝ) / source i) L (𝓝 1) :=
    matrixDimensionRatio_max_source_tendsto source target (fun i => NeZero.pos (source i)) L hratio
  have hsource : (matrixInternalQuotient source A L).map
      (matrixCanonicalSourceToCommon source target (fun i => NeZero.pos (source i)) L hratio).toStarAlgHom =
      matrixInternalQuotient N A' L :=
    matrixFrameQuotientHom_internal_map source N
      (fun i => matrixCanonicalCornerFrame (Nat.le_max_left (source i) (target i)))
      (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_left (source i) (target i)))
      (fun i => NeZero.pos (source i)) hN L hrS A
  have htarget : (matrixInternalQuotient target B L).map
      (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom =
      matrixInternalQuotient N A' L :=
    matrixDimensionCutTarget_canonical_map N target S hd T ht hrN
  refine ⟨B, ?_, ?_⟩
  · apply StarSubalgebra.map_injective (matrixCanonicalTargetToCommon source target ht L hratio).injective
    rw [StarSubalgebra.map_map]
    change (matrixInternalQuotient source A L).map
      ((matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom.comp
        (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom) =
      (matrixInternalQuotient target B L).map
        (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom
    have hc : (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom.comp
        (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom =
        (matrixCanonicalSourceToCommon source target (fun i => NeZero.pos (source i)) L hratio).toStarAlgHom := by
      ext x
      exact matrixCanonicalDimensionEquiv_to_common source target (fun i => NeZero.pos (source i)) ht L hratio x
    rw [hc, hsource, htarget]
  · let δ : ι → ℝ := fun i =>
      2 * Real.sqrt (2 * matrixTraceReal (N i) (1 - (S i).frame * (S i).frameᴴ)) +
        8 * Real.sqrt (matrixTraceReal (N i) (1 - (S i).frame * (S i).frameᴴ))
    have hδ : Tendsto δ L (𝓝 0) := matrixDimensionCutTarget_error_tendsto N target S hd
      (matrixDimensionRatio_inverse_tendsto target N L hrN)
    have hb (i : ι) : matrixHSUnitBallHausdorff (source i) (A' i) (T i).liftedAlgebra ≤
        Real.sqrt ((N i : ℝ) / source i) * δ i :=
      matrixHSUnitBallHausdorff_bound_rescale (hN i) (A' i) (T i).liftedAlgebra
        (by dsimp only [δ]; positivity) (T i).unitBall_approximations.1 (T i).unitBall_approximations.2
    exact squeeze_zero (fun i => matrixHSUnitBallHausdorff_nonneg _ _ _) hb
      (by simpa using hrS.sqrt.mul hδ)

end ThomGame.Analysis
