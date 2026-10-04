module

public import ThomGame.Analysis.MatrixALTTerminalCoverage
public import ThomGame.Analysis.MatrixLowSpectralComplement
public import ThomGame.Analysis.MatrixALTProposition3_6

/-!
# Orthogonal correction at the terminal ALT state

The proved coverage estimate and the stronger energy bound 9 alpha
verify every input of Proposition 3.6. Its actual partial isometries
also satisfy the low-spectral leakage estimate in ALT (4.11).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixALT_terminal_orthogonalCorrection (U : Fin h → UnitaryMatrix d)
    {R : CMatrix d} (hR : IsStarProjection R) (F : Fin n → CMatrix d)
    (hF : ∀ i, IsStarProjection (F i)) {κ α η : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hηκ : η ≤ κ / 1024) (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (hαη : α ≤ η ^ 4) (hexp : 9 * α ≤ Real.exp (-(η ^ 4)⁻¹))
    (hRtrace : matrixTraceReal d (1 - R) ≤ α)
    (hFtrace : (∑ i, matrixTraceReal d (F i)) ≤ 8 / 3)
    (hFenergy : (∑ i, matrixCoordinateEnergy U (F i)) ≤ 8 * α)
    (hstop : ¬∃ p, MatrixALTSelectionCandidate U κ R ((1 - R) + ∑ i, F i) p) :
    ∃ V : Fin n → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∀ i, ((V i)ᴴ * V i).rank ≤ (F i).rank) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤ 1184 * η ^ 2 ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 4736 * η ^ 2 ∧
      (∑ i : Fin n, matrixTraceReal d
        (matrixProjectionPartialSum (1 - R) (matrixExtendFiniteFamily F) i ^ 2 *
          (V i * (V i)ᴴ))) ≤ 3 * η ∧
      (∑ i : Fin n, matrixTraceReal d
        ((1 - matrixClosedLowSpectralCut
          (matrixProjectionPartialSum (1 - R) (matrixExtendFiniteFamily F) i) (κ / 512)) *
            (V i * (V i)ᴴ))) ≤ 3 * (512 / κ) ^ 2 * η ∧
      IsStarProjection (1 - ∑ i, (V i)ᴴ * V i) ∧
      matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) ≤ 16 * η := by
  have hsumpos : 0 ≤ ∑ i, F i := Finset.sum_nonneg fun i _ => (hF i).nonneg
  have hS : 0 ≤ (1 - R) + ∑ i, F i := add_nonneg hR.one_sub.nonneg hsumpos
  have hSR : 1 - R ≤ (1 - R) + ∑ i, F i := le_add_of_nonneg_right hsumpos
  have hE0 := matrixCoordinateEnergy_projection_le_trace U hR.one_sub
  have hinputE : matrixCoordinateEnergy U (1 - R) + ∑ i, matrixCoordinateEnergy U (F i) ≤ 9 * α := by
    linarith only [hE0, hRtrace, hFenergy]
  have hsqrt : matrixCoordinateEnergy U (CFC.sqrt ((1 - R) + ∑ i, F i)) ≤ 18 * η ^ 4 := by
    have he := matrixCoordinateEnergy_selected_sum_sqrt_le U hR F hF
    linarith only [he, hinputE, hαη]
  have hcover := matrixALT_terminal_coverage U hS hR hSR hκ hκ1 hη.le (by linarith) hηκ hsmall
    (hRtrace.trans hαη) hstop hsqrt
  have htrace : (normalizedTrace (1 - R)).re + (∑ i, (normalizedTrace (F i)).re) ≤ 3 := by
    have hpow : η ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by gcongr
    simp only [normalizedTrace_re]
    change matrixTraceReal d (1 - R) + (∑ i, matrixTraceReal d (F i)) ≤ 3
    norm_num at hpow
    linarith only [hRtrace, hαη, hpow, hFtrace]
  have hcover' : (normalizedTrace (1 - R)).re +
      (normalizedTrace (matrixClosedLowSpectralCut ((1 - R) + ∑ i, F i) η)).re ≤ η := by
    simpa only [normalizedTrace_re, matrixTraceReal] using hcover
  obtain ⟨V, hVi, hVf, horth, hrank, hVe, hPe, hweight, hP0, htrace0⟩ :=
    exists_matrixOrthogonalCorrection_ALT_proposition3_6 hη hη8 hR F hF U htrace (hinputE.trans hexp) hcover'
  have hw : (∑ i : Fin n, matrixTraceReal d
      (matrixProjectionPartialSum (1 - R) (matrixExtendFiniteFamily F) i ^ 2 * (V i * (V i)ᴴ))) ≤ 3 * η := by
    simpa only [normalizedTrace_re, matrixTraceReal] using hweight
  refine ⟨V, hVi, hVf, horth, hrank, hVe, hPe, hw, ?_, hP0, ?_⟩
  · exact matrixTraceReal_lowCut_complement_sum_le
      (fun i : Fin n => matrixProjectionPartialSum (1 - R) (matrixExtendFiniteFamily F) i)
      (fun i => V i * (V i)ᴴ)
      (fun i => matrixProjectionPartialSum_nonneg hR.one_sub.nonneg (matrixExtendFiniteFamily F)
        (matrixExtendFiniteFamily_projection F hF) i) hVf hκ hw
  · simpa only [normalizedTrace_re, matrixTraceReal] using htrace0

end ThomGame.Analysis
