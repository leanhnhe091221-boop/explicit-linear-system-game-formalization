module

public import ThomGame.Analysis.MatrixALTSelectionExpansion
public import ThomGame.Analysis.MatrixProjectionSumSqrtEnergy
public import ThomGame.Analysis.MatrixClosedLowSpectralCoarea
public import ThomGame.Analysis.MatrixALTCorrectionTransfer

/-!
# Coverage at the terminal ALT selection state

The threshold is in the exact source interval [kappa/1024,kappa/512].
Closed-cut coarea and stopping give explicit energy and trace estimates.
These estimates supply the coverage hypothesis of Proposition 3.6.
-/

@[expose] public section
namespace ThomGame.Analysis

open Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] [NeZero h]

theorem matrixCoordinateEnergy_projection_le_trace (U : Fin h → UnitaryMatrix d)
    {p : CMatrix d} (hp : IsStarProjection p) : matrixCoordinateEnergy U p ≤ matrixTraceReal d p := by
  have he := matrixCoordinateEnergy_le_hsNorm_sq U p
  rwa [hsNorm_projection_sq hp, normalizedTrace_re] at he

omit [NeZero d] [NeZero h] in
theorem matrixCoordinateEnergy_selected_sum_sqrt_le {n : Nat} (U : Fin h → UnitaryMatrix d)
    {R : CMatrix d} (hR : IsStarProjection R) (F : Fin n → CMatrix d)
    (hF : ∀ i, IsStarProjection (F i)) :
    matrixCoordinateEnergy U (CFC.sqrt ((1 - R) + ∑ i, F i)) ≤
      2 * (matrixCoordinateEnergy U (1 - R) + ∑ i, matrixCoordinateEnergy U (F i)) := by
  let G : Option (Fin n) → CMatrix d
    | none => 1 - R
    | some i => F i
  have hG : ∀ i, IsStarProjection (G i) := by
    intro i
    cases i with
    | none => exact hR.one_sub
    | some i => exact hF i
  simpa only [Fintype.sum_option, G] using matrixCoordinateEnergy_projection_sum_sqrt_le U G hG

theorem exists_matrixALT_lowCut_energy_le (U : Fin h → UnitaryMatrix d)
    {S : CMatrix d} (hS : 0 ≤ S) {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ ∈ Icc (κ / 1024) (κ / 512), matrixCoordinateEnergy U (matrixClosedLowSpectralCut S θ) ≤
      48 / Real.sqrt κ * Real.sqrt (matrixCoordinateEnergy U (CFC.sqrt S)) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  obtain ⟨θ, hθ, he⟩ := exists_matrixClosedLowSpectralCut_sqrt_energy_le U hS
    (a := Real.sqrt κ / 32) (b := Real.sqrt κ / 24) (by positivity) (by linarith)
  have ha : (Real.sqrt κ / 32) ^ 2 = κ / 1024 := by rw [div_pow, Real.sq_sqrt hκ.le]; norm_num
  have hb : (Real.sqrt κ / 24) ^ 2 = κ / 576 := by rw [div_pow, Real.sq_sqrt hκ.le]; norm_num
  rw [ha, hb] at hθ
  refine ⟨θ, ⟨hθ.1, hθ.2.trans (by linarith)⟩, ?_⟩
  convert he using 1
  rw [show 2 * (Real.sqrt κ / 24 - Real.sqrt κ / 32) = Real.sqrt κ / 48 by ring]
  simp only [div_eq_mul_inv]
  ring

theorem exists_matrixALT_terminal_lowCut (U : Fin h → UnitaryMatrix d)
    {S R : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ η : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hstop : ¬∃ p, MatrixALTSelectionCandidate U κ R S p)
    (henergy : matrixCoordinateEnergy U (CFC.sqrt S) ≤ 18 * η ^ 4) :
    ∃ θ ∈ Icc (κ / 1024) (κ / 512),
      matrixCoordinateEnergy U (matrixClosedLowSpectralCut S θ) ≤ 240 / Real.sqrt κ * η ^ 2 ∧
      matrixTraceReal d (matrixClosedLowSpectralCut S θ) ≤ 61440 / (κ * Real.sqrt κ) * η ^ 2 := by
  obtain ⟨θ, hθ, he⟩ := exists_matrixALT_lowCut_energy_le U hS hκ
  have hs : Real.sqrt (matrixCoordinateEnergy U (CFC.sqrt S)) ≤ 5 * η ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (η ^ 2)]
  have he' : matrixCoordinateEnergy U (matrixClosedLowSpectralCut S θ) ≤ 240 / Real.sqrt κ * η ^ 2 := by
    calc
      _ ≤ _ := he
      _ ≤ 48 / Real.sqrt κ * (5 * η ^ 2) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hexp := matrixALTSelection_terminal_expansion U hS hR hSR hκ1 hstop
    (matrixClosedLowSpectralCut_isStarProjection S θ) (matrixClosedLowSpectralCut_mono S hθ.2)
  have ht : matrixTraceReal d (matrixClosedLowSpectralCut S θ) ≤
      256 / κ * matrixCoordinateEnergy U (matrixClosedLowSpectralCut S θ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    linarith only [hexp]
  refine ⟨θ, hθ, he', ?_⟩
  calc
    _ ≤ _ := ht
    _ ≤ 256 / κ * (240 / Real.sqrt κ * η ^ 2) := mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by ring

theorem matrixALT_terminal_coverage (U : Fin h → UnitaryMatrix d)
    {S R : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ η : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hηκ : η ≤ κ / 1024)
    (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (htrace : matrixTraceReal d (1 - R) ≤ η ^ 4)
    (hstop : ¬∃ p, MatrixALTSelectionCandidate U κ R S p)
    (henergy : matrixCoordinateEnergy U (CFC.sqrt S) ≤ 18 * η ^ 4) :
    matrixTraceReal d (1 - R) + matrixTraceReal d (matrixClosedLowSpectralCut S η) ≤ η := by
  obtain ⟨θ, hθ, _, ht⟩ := exists_matrixALT_terminal_lowCut U hS hR hSR hκ hκ1 hstop henergy
  have hm := matrixTraceReal_mono d (matrixClosedLowSpectralCut_mono S (hηκ.trans hθ.1))
  have hpow : η ^ 4 ≤ η ^ 2 := by
    have he : η ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (η ^ 2), sq_nonneg η]
  have hb := mul_le_mul_of_nonneg_right hsmall hη
  nlinarith only [htrace, ht, hm, hpow, hb]

end ThomGame.Analysis
