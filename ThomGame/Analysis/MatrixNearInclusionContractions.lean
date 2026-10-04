module

public import ThomGame.Analysis.MatrixNearInclusion
public import ThomGame.Analysis.MatrixFrameStabilizationBounds

/-!
# Contraction witnesses and dimension changes, including dimension zero

Conditional expectation gives a contraction witness for near inclusion.
The exact normalization formula also holds for zero-sized matrices,
where both norms vanish.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem matrixNearInclusion_contraction {d : Nat}
    (B A : StarSubalgebra ℂ (CMatrix d)) {ε : ℝ}
    (hnear : MatrixNearInclusion B A ε)
    (X : CMatrix d) (hX : X ∈ B) (hn : matrixOpNorm X ≤ 1) :
    ∃ Y ∈ A, matrixOpNorm Y ≤ 1 ∧ hsNorm (X - Y) ≤ ε := by
  by_cases hd : d = 0
  · subst d
    obtain ⟨Y, hY, he⟩ := hnear X hX hn
    refine ⟨Y, hY, ?_, he⟩
    have hYX : Y = X := Subsingleton.elim _ _
    rwa [hYX]
  · let : NeZero d := ⟨hd⟩
    obtain ⟨Y, hY, he⟩ := hnear X hX hn
    exact ⟨matrixTraceProjection A X, matrixTraceProjection_mem A X,
      (matrixTraceProjection_matrixOpNorm_le A X).trans hn,
      (matrixTraceProjection_bestApproximation A X Y hY).trans he⟩

theorem rectHSNorm_dimension_rescale {r d : Nat} (hr : 0 < r) (X : CMatrix d) :
    rectHSNorm r X = Real.sqrt ((d : ℝ) / r) * hsNorm X := by
  by_cases hd : d = 0
  · subst d
    have hX : X = 0 := Subsingleton.elim _ _
    simp [hX]
  · rw [rectHSNorm_rescale hr (Nat.pos_of_ne_zero hd), rectHSNorm_eq_hsNorm]

end ThomGame.Analysis
