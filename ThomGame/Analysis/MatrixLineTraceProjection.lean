module

public import ThomGame.Analysis.MatrixSubmoduleTraceProjection
public import ThomGame.Analysis.MatrixRectangleLineProjection

/-!
# Ambient and rectangular trace projections onto the same matrix line
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} [NeZero d]

omit [NeZero d] in
theorem matrixSubmoduleTraceHilbert_singleton (W : CMatrix d) :
    matrixSubmoduleTraceHilbert (ℂ ∙ W) = ℂ ∙ finiteMatrixHilbertEquiv d W := by
  ext z
  constructor
  · intro hz
    change (finiteMatrixHilbertEquiv d).symm z ∈ ℂ ∙ W at hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply (finiteMatrixHilbertEquiv d).symm.injective
    simpa only [map_smul, LinearEquiv.symm_apply_apply] using hc
  · intro hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    change (finiteMatrixHilbertEquiv d).symm z ∈ ℂ ∙ W
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    have h := congrArg (finiteMatrixHilbertEquiv d).symm hc
    simpa only [map_smul, LinearEquiv.symm_apply_apply] using h

theorem matrixSubmoduleTraceProjection_singleton (W X : CMatrix d) :
    matrixSubmoduleTraceProjection (ℂ ∙ W) X =
      (normalizedTrace (star W * X) / ((hsNorm W ^ 2 : ℝ) : ℂ)) • W := by
  apply (finiteMatrixHilbertEquiv d).injective
  rw [matrixSubmoduleTraceProjection_embedding, map_smul]
  simp only [matrixSubmoduleTraceHilbert_singleton]
  rw [Submodule.starProjection_singleton]
  change (inner ℂ (finiteMatrixHilbertEquiv d W) (finiteMatrixHilbertEquiv d X) /
    ((‖finiteMatrixHilbertEquiv d W‖ ^ 2 : ℝ) : ℂ)) • finiteMatrixHilbertEquiv d W = _
  rw [finiteMatrixHilbert_inner, finiteMatrixHilbert_norm]

theorem matrixRectangleLineProjection_apply_matrix (P Q W X : CMatrix d)
    (hWl : P * W = W) (hWr : W * Q = W) (hXl : P * X = X) (hXr : X * Q = X) :
    (finiteMatrixHilbertEquiv d).symm
      ((matrixRectangleLineProjection P Q W hWl hWr) (matrixRectangleVector P Q X hXl hXr)).val =
        matrixSubmoduleTraceProjection (ℂ ∙ W) X := by
  rw [matrixSubmoduleTraceProjection_singleton]
  change (finiteMatrixHilbertEquiv d).symm
    (((ℂ ∙ matrixRectangleVector P Q W hWl hWr).starProjection
      (matrixRectangleVector P Q X hXl hXr)).val) = _
  rw [Submodule.starProjection_singleton]
  change (inner ℂ (matrixRectangleVector P Q W hWl hWr) (matrixRectangleVector P Q X hXl hXr) /
    ((‖matrixRectangleVector P Q W hWl hWr‖ ^ 2 : ℝ) : ℂ)) • W = _
  rw [matrixRectangleVector_norm]
  rfl

end ThomGame.Analysis
