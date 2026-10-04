module

public import ThomGame.Analysis.MatrixProjectionExclusion
public import ThomGame.Analysis.MatrixBadProjectionFamilies

/-!
# Excluding the actual Markov bad projections

The two finite-family estimates yield a projection with small trace
loss. The exact tolerance inequality `beta <= alpha^2/64` bounds the
loss by `alpha`, with no requirement that `alpha` itself be small.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem badProjection_trace_loss_le (κ α β loss : ℝ) (hκ : κ ≤ 1) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβα : β ≤ α ^ 2 / 64) (h₁ : loss ≤ 1)
    (hloss : loss ≤ κ * β ^ 2 / α + 36 * β ^ 2 / α ^ 2) : loss ≤ α := by
  by_cases ha : 1 ≤ α
  · exact h₁.trans ha
  · have ha₁ : α ≤ 1 := le_of_not_ge ha
    have hβa : β ≤ α / 64 := by nlinarith
    have hb₂ : β ^ 2 ≤ α ^ 2 / 4096 := by
      have he := (sq_le_sq₀ hβ (by positivity)).2 hβa
      nlinarith
    have hb₃ : β ^ 2 ≤ α ^ 3 / 4096 := by
      have he := mul_le_mul hβa hβα hβ (by positivity : 0 ≤ α / 64)
      nlinarith
    have hleft : κ * β ^ 2 / α ≤ α / 2 := by
      apply (div_le_iff₀ hα).2
      have hk := mul_le_mul_of_nonneg_right hκ (sq_nonneg β)
      nlinarith
    have hright : 36 * β ^ 2 / α ^ 2 ≤ α / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hα)).2
      nlinarith [pow_nonneg hα.le 3]
    linarith

variable {d h : Nat} [NeZero d]

theorem exists_matrixMarkov_good_projection (U : Fin h → UnitaryMatrix d)
    (κ α : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hα : 0 < α) (k : Nat)
    (hβα : matrixMarkovDefectBound U κ k ≤ α ^ 2 / 64) :
    ∃ R : CMatrix d, IsStarProjection R ∧ (normalizedTrace (1 - R)).re ≤ α ∧
      ∀ P, IsStarProjection P → P ≤ R → ¬MatrixDistanceBad U κ α k P ∧ ¬MatrixEnergyBad U α k P := by
  classical
  obtain ⟨R, hR, htrace, htrace₁, he⟩ := exists_matrixProjection_excluding_two
    (MatrixDistanceBad U κ α k) (MatrixEnergyBad U α k)
    (fun P hP => ⟨hP.1, hP.2.1⟩) (fun P hP => ⟨hP.1, hP.2.1⟩)
    (κ * matrixMarkovDefectBound U κ k ^ 2 / α) (36 * matrixMarkovDefectBound U κ k ^ 2 / α ^ 2)
    (fun s hs horth => by
      have ht := matrixDistanceBad_family_trace_bound U κ α hκ hα k (fun i : s => i.val)
        (fun i => hs i.val i.prop) (fun i j hij => horth i.prop j.prop (fun he => hij (Subtype.ext he)))
      rwa [Finset.sum_coe_sort s (fun P : CMatrix d => (normalizedTrace P).re)] at ht)
    (fun s hs horth => by
      have ht := matrixEnergyBad_family_trace_bound U κ α hα k (fun i : s => i.val)
        (fun i => hs i.val i.prop) (fun i j hij => horth i.prop j.prop (fun he => hij (Subtype.ext he)))
      rwa [Finset.sum_coe_sort s (fun P : CMatrix d => (normalizedTrace P).re)] at ht)
  exact ⟨R, hR, badProjection_trace_loss_le κ α _ _ hκ₁ hα
    (matrixMarkovDefectBound_nonneg U κ k) hβα htrace₁ htrace, he⟩

end ThomGame.Analysis
