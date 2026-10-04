module

public import ThomGame.Analysis.MatrixALTCorrectionTransfer
public import ThomGame.Analysis.ALTCorrectionParameters

/-!
# ALT Proposition 3.6 with explicit constants

For `0 < eta ≤ 1/8`, the actual corrected family has total energy at
most `1184 eta^2`, weighted trace at most `3 eta`, and missing trace
at most `16 eta`. Its initial projections have the prescribed rank
bounds and total energy at most `4736 eta^2`.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixOrthogonalCorrection_ALT_proposition3_6 {η : ℝ} {e : CMatrix d}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (he : IsStarProjection e)
    (F : Fin n → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d)
    (htrace : (normalizedTrace (1 - e)).re + (∑ i, (normalizedTrace (F i)).re) ≤ 3)
    (henergy : matrixCoordinateEnergy U (1 - e) + (∑ i, matrixCoordinateEnergy U (F i)) ≤
      Real.exp (-(η ^ 4)⁻¹))
    (hcover : (normalizedTrace (1 - e)).re +
      (normalizedTrace (matrixClosedLowSpectralCut ((1 - e) + ∑ i, F i) η)).re ≤ η) :
    ∃ V : Fin n → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∀ i, ((V i)ᴴ * V i).rank ≤ (F i).rank) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤ 1184 * η ^ 2 ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 4736 * η ^ 2 ∧
      (∑ i : Fin n, (normalizedTrace
        (matrixProjectionPartialSum (1 - e) (matrixExtendFiniteFamily F) i ^ 2 *
          (V i * (V i)ᴴ))).re) ≤ 3 * η ∧
      IsStarProjection (1 - ∑ i, (V i)ᴴ * V i) ∧
      (normalizedTrace (1 - ∑ i, (V i)ᴴ * V i)).re ≤ 16 * η := by
  obtain ⟨hγ, hγη, hγ4, hγ16, hγt, ht, hscale⟩ := alt_correction_parameters hη hη8
  obtain ⟨q, hq, hqe, hqw, hqc⟩ := exists_matrixFiniteProjectionFamily_ALT_lemma3_3
    hγ hγ4 he F hF U htrace (hγ16.symm ▸ henergy)
  have hqt : ∑ i, matrixTraceReal d (q i) ≤ 3 := by
    have hr : (∑ i, matrixTraceReal d (q i)) ≤ ∑ i, (normalizedTrace (F i)).re := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [normalizedTrace_re, matrixTraceReal] using
        matrixProjection_rank_trace_mono (hq i).1 (hF i) (hq i).2
    have h0 := (Complex.nonneg_iff.mp (normalizedTrace_nonneg (1 - e) he.one_sub.nonneg)).1
    linarith only [hr, h0, htrace]
  obtain ⟨V, hVi, hVf, hVq, horth, hVe, hPe, hVc⟩ :=
    exists_matrixOrthogonalFamily_exponential (fun i => (hq i).1) U hqt (hqe.trans hγt) ht
  rw [hscale] at hVe hPe hVc
  refine ⟨V, hVi, hVf, horth, ?_, ?_, ?_, ?_,
    (matrixOrthogonalSum_projection _ hVi horth).one_sub, ?_⟩
  · intro i
    exact (matrixPartialIsometry_initial_rank_le (hVi i) (hq i).1 (hVq i)).trans (hq i).2
  · linarith only [hVe]
  · linarith only [hPe]
  · have hw : (∑ i : Fin n, (normalizedTrace
          (matrixProjectionPartialSum (1 - e) (matrixExtendFiniteFamily F) i ^ 2 *
            (V i * (V i)ᴴ))).re) ≤
        ∑ i : Fin n, (normalizedTrace
          (matrixProjectionPartialSum (1 - e) (matrixExtendFiniteFamily F) i ^ 2 * q i)).re := by
      apply Finset.sum_le_sum
      intro i _
      have hS := matrixProjectionPartialSum_nonneg he.one_sub.nonneg (matrixExtendFiniteFamily F)
        (matrixExtendFiniteFamily_projection F hF) i
      have hS2 : 0 ≤ matrixProjectionPartialSum (1 - e) (matrixExtendFiniteFamily F) i ^ 2 :=
        hS.isSelfAdjoint.sq_nonneg
      exact normalizedTrace_mul_re_mono hS2 (hVq i)
    linarith only [hw, hqw, hγη]
  · have hl := normalizedTrace_re_mono
      (matrixClosedLowSpectralCut_mono ((1 - e) + ∑ i, F i) hγη)
    have hqcov : matrixFamilyCoverageDefect q ≤ 8 * η := by linarith only [hl, hqc, hcover, hγη]
    rw [matrixFamilyCoverageDefect_orthogonal _ hVi horth] at hVc
    have hηsq := mul_le_mul_of_nonneg_left hη8 hη.le
    nlinarith only [hVc, hqcov, hηsq]

end ThomGame.Analysis
