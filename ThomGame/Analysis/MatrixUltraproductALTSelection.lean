module

public import ThomGame.Analysis.MatrixALTSelectionFamily
public import ThomGame.Analysis.MatrixUltraproductProjectionImprovement

/-!
# ALT Step 1 from the genuine ultraproduct spectral gap

The large coordinate projections and vanishing tolerances are those
constructed in Theorem 2.4. The actual finite selection runs on each
coordinate, with no added improvement or termination hypothesis.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem exists_matrixUltraproduct_ALT_selection (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ (R : (k : Nat) → CMatrix (dims k)) (α : Nat → ℝ),
      (∀ k, 0 < α k) ∧ Tendsto α (L : Filter Nat) (𝓝 0) ∧ ∀ k,
        IsStarProjection (R k) ∧ (normalizedTrace (1 - R k)).re ≤ α k ∧
        ∃ m ≤ 8 * dims k, ∃ (S : Nat → CMatrix (dims k)) (P F : Fin m → CMatrix (dims k)),
          S 0 = 1 - R k ∧ (∀ i, 1 - R k ≤ S i) ∧
          (∀ i : Fin m, MatrixALTSelectionCandidate (U k) κ (R k) (S i) (P i) ∧
            (∀ q, MatrixALTSelectionCandidate (U k) κ (R k) (S i) q → (P i).rank ≤ q.rank) ∧
            MatrixProjectionImprovement (U k) κ (α k) (P i) (F i) ∧ S (i.val + 1) = S i + F i) ∧
          (¬∃ p, MatrixALTSelectionCandidate (U k) κ (R k) (S m) p) ∧
          S m = (1 - R k) + ∑ i, F i ∧
          (∑ i, matrixTraceReal (dims k) (P i)) ≤ 8 ∧
          (∑ i, matrixTraceReal (dims k) (F i)) ≤ 8 / 3 ∧
          (∑ i, matrixCoordinateEnergy (U k) (F i)) ≤ 8 * α k := by
  obtain ⟨R, α, hα, hlim, hR⟩ :=
    exists_matrixUltraproduct_projection_improvement dims U hd L hL κ hgap
  refine ⟨R, α, hα, hlim, ?_⟩
  intro k
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  obtain ⟨hRp, hRt, hcorrect⟩ := hR k
  exact ⟨hRp, hRt, exists_matrixALTSelection_family (U k) hgap.1 hgap.2.1.le (hα k).le hRp hcorrect⟩

end ThomGame.Analysis
