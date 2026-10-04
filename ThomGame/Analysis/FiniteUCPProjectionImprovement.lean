module

public import ThomGame.Analysis.FiniteUCPDefect
public import ThomGame.Analysis.MatrixBadProjectionExclusion
public import ThomGame.Analysis.MatrixMarkovProjectionImprovement
public import ThomGame.Analysis.CPMapSchwarz

/-!
# Projection improvement from arbitrary completely positive smoothing

A trace-preserving completely positive map satisfying the finite ALT input
estimates supplies the same large projection and projection improvements as a
Markov power. Unitality, self-adjointness, and commutation with the Markov map
are unnecessary for this step.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d h : Nat} [NeZero d]

theorem exists_finiteUCP_good_projection (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ α β : ℝ)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hα : 0 < α)
    (hcontrol : FiniteUCPDefectControl U Φ κ β) (hβα : β ≤ α ^ 2 / 64) :
    ∃ R : CMatrix d, IsStarProjection R ∧ (normalizedTrace (1 - R)).re ≤ α ∧
      ∀ P, IsStarProjection P → P ≤ R →
        ¬FiniteUCPDistanceBad U Φ κ α P ∧ ¬FiniteUCPEnergyBad U Φ α P := by
  classical
  obtain ⟨R, hR, htrace, htrace₁, he⟩ := exists_matrixProjection_excluding_two
    (FiniteUCPDistanceBad U Φ κ α) (FiniteUCPEnergyBad U Φ α)
    (fun P hP => ⟨hP.1, hP.2.1⟩) (fun P hP => ⟨hP.1, hP.2.1⟩)
    (κ * β ^ 2 / α) (36 * β ^ 2 / α ^ 2)
    (fun s hs horth => by
      have ht := finiteUCPDistanceBad_family_trace_bound U Φ κ α β hκ hα hcontrol
        (fun i : s => i.val) (fun i => hs i.val i.prop)
        (fun i j hij => horth i.prop j.prop (fun he => hij (Subtype.ext he)))
      rwa [Finset.sum_coe_sort s (fun P : CMatrix d => (normalizedTrace P).re)] at ht)
    (fun s hs horth => by
      have ht := finiteUCPEnergyBad_family_trace_bound U Φ κ α β hα hcontrol
        (fun i : s => i.val) (fun i => hs i.val i.prop)
        (fun i j hij => horth i.prop j.prop (fun he => hij (Subtype.ext he)))
      rwa [Finset.sum_coe_sort s (fun P : CMatrix d => (normalizedTrace P).re)] at ht)
  exact ⟨R, hR, badProjection_trace_loss_le κ α β _ hκ₁ hα
    hcontrol.beta_nonneg hβα htrace₁ htrace, he⟩

variable [NeZero h]

omit [NeZero d] in
theorem exists_finiteUCPProjection_improvement_of_not_bad (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    (κ α : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) {P : CMatrix d}
    (hP : IsStarProjection P)
    (hD : ¬FiniteUCPDistanceBad U Φ.toLinearMap κ α P)
    (hE : ¬FiniteUCPEnergyBad U Φ.toLinearMap α P)
    (hthreshold : matrixCoordinateEnergy U P ≤ κ * (normalizedTrace P).re / 64) :
    ∃ F, MatrixProjectionImprovement U κ α P F := by
  by_cases hp₀ : P = 0
  · subst P
    exact ⟨0, matrixProjectionImprovement_self U κ α hκ hP (by simp [matrixCoordinateEnergy])⟩
  by_cases he : matrixCoordinateEnergy U P ≤ α * (normalizedTrace P).re
  · exact ⟨P, matrixProjectionImprovement_self U κ α hκ hP he⟩
  have hbig : α * (normalizedTrace P).re ≤ matrixCoordinateEnergy U P := le_of_not_ge he
  have hdist : hsNorm (P - Φ P) ≤
      2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U P) :=
    le_of_not_gt (fun hd => hD ⟨hP, hp₀, hbig, hd⟩)
  have hdist₂ : hsNorm (Φ P - P) ^ 2 ≤ 4 * κ⁻¹ * matrixCoordinateEnergy U P := by
    rw [hsNorm_sub_comm]
    have hs := (sq_le_sq₀ (hsNorm_nonneg _) (by positivity)).2 hdist
    simpa only [mul_pow, inv_pow, Real.sq_sqrt hκ.le,
      Real.sq_sqrt (matrixCoordinateEnergy_nonneg U P), show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
  have henergy : matrixCoordinateEnergy U (Φ P) ≤ α ^ 2 * (normalizedTrace P).re / 36 :=
    le_of_not_gt (fun he => hE ⟨hP, hp₀, he⟩)
  exact exists_matrixProjection_improvement_of_estimates hP
    (Matrix.nonneg_iff_posSemidef.mp (map_nonneg Φ hP.nonneg)) U κ α hκ hα
    (congrArg Complex.re (htrace P)) hdist₂ henergy hthreshold

theorem exists_finiteUCP_projection_improvement (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    (κ α β : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hα : 0 < α)
    (hcontrol : FiniteUCPDefectControl U Φ.toLinearMap κ β) (hβα : β ≤ α ^ 2 / 64) :
    ∃ R : CMatrix d, IsStarProjection R ∧ (normalizedTrace (1 - R)).re ≤ α ∧
      ∀ P, IsStarProjection P → P ≤ R →
        matrixCoordinateEnergy U P ≤ κ * (normalizedTrace P).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α P F := by
  obtain ⟨R, hR, ht, hex⟩ := exists_finiteUCP_good_projection U Φ.toLinearMap κ α β
    hκ hκ₁ hα hcontrol hβα
  refine ⟨R, hR, ht, ?_⟩
  intro P hP hPR henergy
  exact exists_finiteUCPProjection_improvement_of_not_bad U Φ htrace κ α hκ hα.le hP
    (hex P hP hPR).1 (hex P hP hPR).2 henergy

end ThomGame.Analysis
