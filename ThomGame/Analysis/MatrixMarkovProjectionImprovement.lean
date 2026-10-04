module

public import ThomGame.Analysis.MatrixBadProjectionExclusion
public import ThomGame.Analysis.MatrixProjectionImprovementStep

/-!
# Projection improvement for actual finite matrix Markov maps

The large projection excludes both bad predicates. Spectral rounding
then supplies all three estimates in ALT (2.8) for every projection
below it satisfying the stated energy threshold.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat}

def MatrixProjectionImprovement (U : Fin h → UnitaryMatrix d) (κ α : ℝ) (P F : CMatrix d) : Prop :=
  IsStarProjection F ∧ hsNorm (F - P) ^ 2 ≤ 36 * κ⁻¹ * matrixCoordinateEnergy U P ∧
    (1 / 3 : ℝ) * (normalizedTrace P).re ≤ (normalizedTrace F).re ∧
    (normalizedTrace F).re ≤ (5 / 3 : ℝ) * (normalizedTrace P).re ∧
    matrixCoordinateEnergy U F ≤ α * (normalizedTrace P).re

theorem matrixLazyMarkov_pow_nonneg (U : Fin h → UnitaryMatrix d) (k : Nat)
    (P : CMatrix d) (hP : 0 ≤ P) : 0 ≤ (matrixLazyMarkov U ^ k) P := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact matrixLazyMarkov_nonneg U _ ih

theorem matrixProjectionImprovement_self (U : Fin h → UnitaryMatrix d) (κ α : ℝ) (hκ : 0 < κ)
    {P : CMatrix d} (hP : IsStarProjection P) (he : matrixCoordinateEnergy U P ≤ α * (normalizedTrace P).re) :
    MatrixProjectionImprovement U κ α P P := by
  have ht := (Complex.nonneg_iff.mp (normalizedTrace_nonneg P hP.nonneg)).1
  refine ⟨hP, ?_, ?_, ?_, he⟩
  · simp only [sub_self, hsNorm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (by positivity) (matrixCoordinateEnergy_nonneg U P)
  · linarith
  · linarith

variable [NeZero d] [NeZero h]

theorem exists_matrixProjection_improvement_of_not_bad (U : Fin h → UnitaryMatrix d)
    (κ α : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) (k : Nat) {P : CMatrix d}
    (hP : IsStarProjection P) (hD : ¬MatrixDistanceBad U κ α k P) (hE : ¬MatrixEnergyBad U α k P)
    (hthreshold : matrixCoordinateEnergy U P ≤ κ * (normalizedTrace P).re / 64) :
    ∃ F, MatrixProjectionImprovement U κ α P F := by
  by_cases hp₀ : P = 0
  · subst P
    exact ⟨0, matrixProjectionImprovement_self U κ α hκ hP (by simp [matrixCoordinateEnergy])⟩
  by_cases he : matrixCoordinateEnergy U P ≤ α * (normalizedTrace P).re
  · exact ⟨P, matrixProjectionImprovement_self U κ α hκ hP he⟩
  have hbig : α * (normalizedTrace P).re ≤ matrixCoordinateEnergy U P := le_of_not_ge he
  have hdist : hsNorm (P - (matrixLazyMarkov U ^ k) P) ≤
      2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U P) := by
    exact le_of_not_gt (fun hd => hD ⟨hP, hp₀, hbig, hd⟩)
  have hdist₂ : hsNorm ((matrixLazyMarkov U ^ k) P - P) ^ 2 ≤ 4 * κ⁻¹ * matrixCoordinateEnergy U P := by
    rw [hsNorm_sub_comm]
    have hs := (sq_le_sq₀ (hsNorm_nonneg _) (by positivity)).2 hdist
    simpa only [mul_pow, inv_pow, Real.sq_sqrt hκ.le,
      Real.sq_sqrt (matrixCoordinateEnergy_nonneg U P), show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
  have henergy : matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) P) ≤
      α ^ 2 * (normalizedTrace P).re / 36 :=
    le_of_not_gt (fun he => hE ⟨hP, hp₀, he⟩)
  exact exists_matrixProjection_improvement_of_estimates hP
    (Matrix.nonneg_iff_posSemidef.mp (matrixLazyMarkov_pow_nonneg U k P hP.nonneg)) U κ α hκ hα
    (congrArg Complex.re (matrixLazyMarkov_pow_trace U k P)) hdist₂ henergy hthreshold

theorem exists_matrixMarkov_projection_improvement (U : Fin h → UnitaryMatrix d)
    (κ α : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hα : 0 < α) (k : Nat)
    (hβα : matrixMarkovDefectBound U κ k ≤ α ^ 2 / 64) :
    ∃ R : CMatrix d, IsStarProjection R ∧ (normalizedTrace (1 - R)).re ≤ α ∧
      ∀ P, IsStarProjection P → P ≤ R → matrixCoordinateEnergy U P ≤ κ * (normalizedTrace P).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α P F := by
  obtain ⟨R, hR, ht, hex⟩ := exists_matrixMarkov_good_projection U κ α hκ hκ₁ hα k hβα
  refine ⟨R, hR, ht, ?_⟩
  intro P hP hPR henergy
  exact exists_matrixProjection_improvement_of_not_bad U κ α hκ hα.le k hP
    (hex P hP hPR).1 (hex P hP hPR).2 henergy

end ThomGame.Analysis
