module

public import ThomGame.Analysis.MatrixMarkovPoincare

/-!
# The attained uniform defect on the matrix contraction ball

This is the actual supremum in ALT (2.9), realized by a maximizing
contraction. It simultaneously bounds the Poincare distance defect
and the boundary energy of the Markov output, and lies in [0, 2].
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d h : Nat} (U : Fin h → UnitaryMatrix d) (κ : ℝ) (k : Nat)

noncomputable def matrixMarkovDefect (X : CMatrix d) : ℝ :=
  max (max (hsNorm (X - (matrixLazyMarkov U ^ k) X) -
    (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X)) 0)
    (Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) X)))

theorem matrixMarkovDefect_nonneg (X : CMatrix d) : 0 ≤ matrixMarkovDefect U κ k X :=
  (Real.sqrt_nonneg _).trans (le_max_right _ _)

variable [NeZero d]

theorem matrixMarkovDefect_continuous : Continuous (matrixMarkovDefect U κ k) := by
  have hc : Continuous (matrixLazyMarkov U ^ k : CMatrix d →ₗ[ℂ] CMatrix d) :=
    (matrixLazyMarkov U ^ k).continuous_of_finiteDimensional
  exact (((continuous_hsNorm.comp (continuous_id.sub hc)).sub
    ((Real.continuous_sqrt.comp (matrixCoordinateEnergy_continuous U)).const_mul _)).max continuous_const).max
      (Real.continuous_sqrt.comp ((matrixCoordinateEnergy_continuous U).comp hc))

theorem exists_matrixMarkovDefect_maximizer : ∃ X : CMatrix d, matrixOpNorm X ≤ 1 ∧
    ∀ Y : CMatrix d, matrixOpNorm Y ≤ 1 → matrixMarkovDefect U κ k Y ≤ matrixMarkovDefect U κ k X := by
  obtain ⟨X, hX, hm⟩ := (isCompact_closedBall (0 : CMatrix d) 1).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr zero_le_one) (matrixMarkovDefect_continuous U κ k).continuousOn
  refine ⟨X, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right, matrixOpNorm] using hX
  · intro Y hY
    exact hm (by simpa only [Metric.mem_closedBall, dist_zero_right, matrixOpNorm] using hY)

noncomputable def matrixMarkovDefectMaximizer : CMatrix d :=
  Classical.choose (exists_matrixMarkovDefect_maximizer U κ k)

theorem matrixMarkovDefectMaximizer_norm_le : matrixOpNorm (matrixMarkovDefectMaximizer U κ k) ≤ 1 :=
  (Classical.choose_spec (exists_matrixMarkovDefect_maximizer U κ k)).1

noncomputable def matrixMarkovDefectBound : ℝ :=
  matrixMarkovDefect U κ k (matrixMarkovDefectMaximizer U κ k)

theorem matrixMarkovDefect_le_bound (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixMarkovDefect U κ k X ≤ matrixMarkovDefectBound U κ k :=
  (Classical.choose_spec (exists_matrixMarkovDefect_maximizer U κ k)).2 X hX

theorem matrixMarkovDefectBound_nonneg : 0 ≤ matrixMarkovDefectBound U κ k :=
  matrixMarkovDefect_nonneg U κ k _

theorem matrixMarkovDefectBound_distance (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - (matrixLazyMarkov U ^ k) X) ≤
      (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) + matrixMarkovDefectBound U κ k := by
  have he := (le_max_left _ _).trans ((le_max_left _ _).trans (matrixMarkovDefect_le_bound U κ k X hX))
  change hsNorm (X - (matrixLazyMarkov U ^ k) X) -
    (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) ≤ _ at he
  linarith

theorem matrixMarkovDefectBound_energy (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) X)) ≤ matrixMarkovDefectBound U κ k :=
  (le_max_right _ _).trans (matrixMarkovDefect_le_bound U κ k X hX)

variable [NeZero h]

theorem matrixMarkovDefect_le_two (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixMarkovDefect U κ k X ≤ 2 := by
  have hx : hsNorm X ≤ 1 := (hsNorm_le_matrixOpNorm X).trans hX
  have hf : hsNorm ((matrixLazyMarkov U ^ k) X) ≤ 1 := (matrixLazyMarkov_pow_hsNorm_le U k X).trans hx
  have hd : hsNorm (X - (matrixLazyMarkov U ^ k) X) ≤ 2 := by
    have he := hsNorm_add_le X (-((matrixLazyMarkov U ^ k) X))
    rw [hsNorm_neg, ← sub_eq_add_neg] at he
    linarith
  apply max_le
  · apply max_le
    · exact (sub_le_self _ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).trans hd
    · norm_num
  · exact (matrixCoordinateEnergy_sqrt_le_hsNorm U _).trans (hf.trans (by norm_num))

theorem matrixMarkovDefectBound_le_two : matrixMarkovDefectBound U κ k ≤ 2 :=
  matrixMarkovDefect_le_two U κ k _ (matrixMarkovDefectMaximizer_norm_le U κ k)

end ThomGame.Analysis
