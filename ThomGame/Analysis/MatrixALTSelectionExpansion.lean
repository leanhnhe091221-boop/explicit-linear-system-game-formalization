module

public import ThomGame.Analysis.MatrixALTSelectionFamily

/-!
# Expansion from stopping and minimum-rank selection

The actual polar transport converts the absence of a small-boundary
candidate into the kappa/256 expansion estimate on the low spectral
space. Minimum rank gives the same estimate below the selected rank.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero h]

theorem matrixALTSelection_expansion_of_not_candidate (U : Fin h → UnitaryMatrix d)
    {S R p : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : κ ≤ 1) (hp : IsStarProjection p)
    (hpb : p ≤ matrixClosedLowSpectralCut S (κ / 512))
    (hnot : ¬MatrixALTSelectionCandidate U κ R S
      (matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)) * p *
        (matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)))ᴴ)) :
    κ / 256 * matrixTraceReal d p ≤ matrixCoordinateEnergy U p := by
  let b := matrixClosedLowSpectralCut S (κ / 512)
  let w := matrixRectPolar (R * b)
  let q := w * p * wᴴ
  obtain ⟨_, _, _, htransport⟩ := matrixALT_lowSpectral_polar_transport U hS hR hSR hκ
  obtain ⟨hq, _, htrace, _, _, henergy⟩ := htransport p hp hpb
  have hlarge : κ / 64 * matrixTraceReal d q ≤ matrixCoordinateEnergy U q := by
    by_cases hz : q = 0
    · simp only [hz, matrixTraceReal_zero, mul_zero]
      exact matrixCoordinateEnergy_nonneg U 0
    · apply le_of_not_gt
      intro he
      exact hnot ⟨hq, hz, matrixProjection_conjugate_le_gram hp w, he⟩
  change κ / 64 * matrixTraceReal d q ≤ matrixCoordinateEnergy U q at hlarge
  change matrixTraceReal d q = matrixTraceReal d p at htrace
  change matrixCoordinateEnergy U q ≤ 2 * matrixCoordinateEnergy U p + κ / 128 * matrixTraceReal d p at henergy
  rw [htrace] at hlarge
  linarith only [hlarge, henergy]

theorem matrixALTSelection_terminal_expansion (U : Fin h → UnitaryMatrix d)
    {S R : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : κ ≤ 1) (hstop : ¬∃ q, MatrixALTSelectionCandidate U κ R S q)
    {p : CMatrix d} (hp : IsStarProjection p)
    (hpb : p ≤ matrixClosedLowSpectralCut S (κ / 512)) :
    κ / 256 * matrixTraceReal d p ≤ matrixCoordinateEnergy U p :=
  matrixALTSelection_expansion_of_not_candidate U hS hR hSR hκ hp hpb (fun he => hstop ⟨_, he⟩)

theorem matrixALTSelection_minimal_rank_expansion (U : Fin h → UnitaryMatrix d)
    {S R P : CMatrix d} (hS : 0 ≤ S) (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    {κ : ℝ} (hκ : κ ≤ 1)
    (hmin : ∀ q, MatrixALTSelectionCandidate U κ R S q → P.rank ≤ q.rank)
    {p : CMatrix d} (hp : IsStarProjection p)
    (hpb : p ≤ matrixClosedLowSpectralCut S (κ / 512)) (hrank : p.rank < P.rank) :
    κ / 256 * matrixTraceReal d p ≤ matrixCoordinateEnergy U p := by
  apply matrixALTSelection_expansion_of_not_candidate U hS hR hSR hκ hp hpb
  intro he
  have hl := hmin _ he
  obtain ⟨_, _, _, htransport⟩ := matrixALT_lowSpectral_polar_transport U hS hR hSR hκ
  have hr := (htransport p hp hpb).2.2.2.1
  rw [hr] at hl
  exact (not_le_of_gt hrank) hl

end ThomGame.Analysis
