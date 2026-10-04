module

public import ThomGame.Quantum.FiniteCommonSpectralCut
public import Mathlib.Tactic.FunProp

/-! Arbitrarily small relative errors on a single nonzero projection, uniformly over dimensions. -/

@[expose] public section
namespace ThomGame.Quantum

open Analysis Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem continuous_systemDensityBudget (R : Type*) [Fintype R] : Continuous (systemDensityBudget R) := by
  unfold systemDensityBudget
  fun_prop

theorem systemDensityBudget_zero (R : Type*) [Fintype R] : systemDensityBudget R 0 = 0 := by
  simp [systemDensityBudget]

theorem exists_small_positive_densityBudget (R : Type*) [Fintype R] {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, 2 * systemDensityBudget R ε ≤ κ := by
  have ht := (continuous_systemDensityBudget R).continuousAt (x := 0)
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp ht (κ / 2) (half_pos hκ)
  have he : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  have hh := hb he
  rw [systemDensityBudget_zero, Real.dist_eq, sub_zero,
    abs_of_pos (systemDensityBudget_pos R (half_pos hδ))] at hh
  exact ⟨δ / 2, half_pos hδ, by linarith⟩

end ThomGame.Quantum

namespace ThomGame.SparseSystem

open Quantum Analysis Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] (S : SparseSystem R C)

theorem near_perfect_common_projection {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∀ T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ S.incidenceGame.success T.correlation →
      ∃ P : CMatrix T.dimBob, P ≠ 0 ∧ IsStarProjection P ∧
        (∀ r i, rectHSNorm 1 (P * T.bobMatrix (S.column r i) - T.bobMatrix (S.column r i) * P) ^ 2 ≤
          κ * rectHSNorm 1 P ^ 2) ∧
        (∀ r, rectHSNorm 1 (T.rowMatrixError S r * P) ^ 2 ≤ κ * rectHSNorm 1 P ^ 2) ∧
        (∀ r i j, rectHSNorm 1 (T.commutatorMatrixError S r i j * P) ^ 2 ≤ κ * rectHSNorm 1 P ^ 2) := by
  obtain ⟨ε, hε, he⟩ := exists_small_positive_densityBudget R hκ
  refine ⟨ε, hε, fun T hT => ?_⟩
  obtain ⟨s, _hs, hz, hp, hu, hr⟩ := T.near_perfect_common_spectralCut S hε hT
  have hb : 2 * systemDensityBudget R ε * rectHSNorm 1 (matrixSquareSpectralCut (densityRoot T.state) s) ^ 2 ≤
      κ * rectHSNorm 1 (matrixSquareSpectralCut (densityRoot T.state) s) ^ 2 :=
    mul_le_mul_of_nonneg_right he (sq_nonneg _)
  exact ⟨matrixSquareSpectralCut (densityRoot T.state) s, hz, hp,
    fun r i => (hu r i).trans hb,
    fun r => (hr (Sum.inl r)).trans hb,
    fun r i j => (hr (Sum.inr (r, i, j))).trans hb⟩

end ThomGame.SparseSystem
