module

public import ThomGame.Analysis.MatrixALTOrthogonalSelection
public import ThomGame.Analysis.ALTDecompositionParameters
public import ThomGame.Analysis.MatrixUltraproductProjectionImprovement

/-!
# ALT Steps 1 and 2 under the genuine ultraproduct spectral gap

The actual logarithmic scale verifies all small-parameter conditions
on an ultrafilter-large set. The same minimum-rank choices, corrected
projections and orthogonal partial isometries satisfy (4.9)--(4.11).
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem exists_matrixUltraproduct_ALT_orthogonalSelection (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ (R : (k : Nat) → CMatrix (dims k)) (α : Nat → ℝ),
      (∀ k, 0 < α k) ∧ Tendsto α (L : Filter Nat) (𝓝 0) ∧
      (∀ k, IsStarProjection (R k) ∧ matrixTraceReal (dims k) (1 - R k) ≤ α k) ∧
      Tendsto (fun k => altDecompositionScale (α k)) (L : Filter Nat) (𝓝 0) ∧
      ∀ᶠ k in (L : Filter Nat),
        α k ≤ altDecompositionScale (α k) ^ 4 ∧
        9 * α k ≤ Real.exp (-(altDecompositionScale (α k) ^ 4)⁻¹) ∧
        Nonempty (MatrixALTOrthogonalSelection (U k) κ (α k) (altDecompositionScale (α k)) (R k)) := by
  obtain ⟨R, α, hα, hlim, hR⟩ :=
    exists_matrixUltraproduct_projection_improvement dims U hd L hL κ hgap
  have hRtrace (k : Nat) : matrixTraceReal (dims k) (1 - R k) ≤ α k := by
    simpa only [normalizedTrace_re, matrixTraceReal] using (hR k).2.1
  refine ⟨R, α, hα, hlim, fun k => ⟨(hR k).1, hRtrace k⟩,
    altDecompositionScale_tendsto_zero hα hlim, ?_⟩
  filter_upwards [altDecompositionScale_eventually_admissible hα hlim hgap.1] with k hk
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  obtain ⟨hη8, hηκ, hsmall, hαη, hexp⟩ := hk
  refine ⟨hαη, hexp, ?_⟩
  exact exists_matrixALTOrthogonalSelection (U k) (hR k).1 hgap.1 hgap.2.1.le (hα k).le
    (altDecompositionScale_pos (α k)) hη8 hηκ hsmall hαη hexp (hRtrace k) (hR k).2.2

end ThomGame.Analysis
