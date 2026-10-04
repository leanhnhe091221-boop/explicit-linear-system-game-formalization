module

public import ThomGame.Analysis.MatrixMarkovProjectionImprovement
public import ThomGame.Analysis.MatrixMarkovTolerance

/-!
# ALT Theorem 2.4 for actual matrix ultraproducts

Under the genuine ultraproduct spectral gap, there are actual
coordinate projections and positive tolerances tending to zero.
Every low-energy projection below a chosen coordinate projection
has an improved projection satisfying all three estimates in (2.8).
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n)

theorem exists_matrixMarkov_projection_improvement_diagonal (κ : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    ∃ R : (n : Nat) → CMatrix (dims n), ∀ n,
      IsStarProjection (R n) ∧ (normalizedTrace (1 - R n)).re ≤ matrixMarkovTolerance dims U hd κ n ∧
        ∀ P, IsStarProjection P → P ≤ R n →
          matrixCoordinateEnergy (U n) P ≤ κ * (normalizedTrace P).re / 64 →
            ∃ F, MatrixProjectionImprovement (U n) κ (matrixMarkovTolerance dims U hd κ n) P F := by
  have hn (n : Nat) : ∃ R : CMatrix (dims n), IsStarProjection R ∧
      (normalizedTrace (1 - R)).re ≤ matrixMarkovTolerance dims U hd κ n ∧
      ∀ P, IsStarProjection P → P ≤ R →
        matrixCoordinateEnergy (U n) P ≤ κ * (normalizedTrace P).re / 64 →
          ∃ F, MatrixProjectionImprovement (U n) κ (matrixMarkovTolerance dims U hd κ n) P F := by
    let : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
    apply exists_matrixMarkov_projection_improvement (U n) κ (matrixMarkovTolerance dims U hd κ n)
      hκ hκ₁ (matrixMarkovTolerance_pos dims U hd κ n) (matrixMarkovDiagonalPower dims U hd κ n)
    exact matrixMarkovTolerance_defect_sq_bound dims U hd κ n
  exact ⟨fun n => Classical.choose (hn n), fun n => Classical.choose_spec (hn n)⟩

theorem exists_matrixUltraproduct_projection_improvement (L : Ultrafilter Nat)
    (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ (R : (n : Nat) → CMatrix (dims n)) (α : Nat → ℝ),
      (∀ n, 0 < α n) ∧ Tendsto α (L : Filter Nat) (𝓝 0) ∧ ∀ n,
        IsStarProjection (R n) ∧ (normalizedTrace (1 - R n)).re ≤ α n ∧
          ∀ P, IsStarProjection P → P ≤ R n →
            matrixCoordinateEnergy (U n) P ≤ κ * (normalizedTrace P).re / 64 →
              ∃ F, MatrixProjectionImprovement (U n) κ (α n) P F := by
  obtain ⟨R, hR⟩ := exists_matrixMarkov_projection_improvement_diagonal dims U hd κ hgap.1 hgap.2.1.le
  exact ⟨R, matrixMarkovTolerance dims U hd κ, matrixMarkovTolerance_pos dims U hd κ,
    matrixMarkovTolerance_tendsto_zero dims U hd κ L hL hgap, hR⟩

end ThomGame.Analysis
