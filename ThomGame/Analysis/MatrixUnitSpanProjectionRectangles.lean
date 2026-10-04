module

public import ThomGame.Analysis.MatrixUnitSpanRectangles
public import ThomGame.Analysis.MatrixLineTraceProjection
public import ThomGame.Analysis.MatrixRectanglePairingCompression

/-!
# The actual matrix-unit span projection restricts to the matrix-unit line
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} [NeZero d] {μ : Type*}

theorem matrixUnitSpan_projection_rectangle (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (i j : μ) (X : CMatrix d) (hXl : E i * X = X) (hXr : X * E j = X) :
    matrixSubmoduleTraceProjection (matrixUnitSpan W) X = matrixSubmoduleTraceProjection (ℂ ∙ W i j) X := by
  let Z := matrixSubmoduleTraceProjection (ℂ ∙ W i j) X
  have hZ : Z ∈ ℂ ∙ W i j := matrixSubmoduleTraceProjection_mem (ℂ ∙ W i j) X
  have hline : ℂ ∙ W i j ≤ matrixRectangleSubmodule (E i) (E j) :=
    (Submodule.span_singleton_le_iff_mem (W i j) _).mpr (hsupport i j)
  have hres := (matrixRectangleSubmodule (E i) (E j)).sub_mem ⟨hXl, hXr⟩ (hline hZ)
  apply matrixSubmoduleTraceProjection_unique
  · exact ((Submodule.span_singleton_le_iff_mem (W i j) _).mpr (matrixUnitSpan_unit_mem W i j)) hZ
  · intro B hB
    rw [← matrixRectangle_pairing_compress_left (E i) (E j) (X - Z) B (hE i) (hE j) hres.1 hres.2]
    exact matrixSubmoduleTraceProjection_orthogonal (ℂ ∙ W i j) X (E i * B * E j)
      (matrixUnitSpan_compression_mem_line E W horth hsupport i j hB)

theorem matrixUnitSpan_projection_invariant (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j) (i j : μ) :
    ∀ X ∈ matrixRectangleSubmodule (E i) (E j),
      matrixSubmoduleTraceProjection (matrixUnitSpan W) X ∈ matrixRectangleSubmodule (E i) (E j) := by
  intro X hX
  rw [matrixUnitSpan_projection_rectangle E W hE horth hsupport i j X hX.1 hX.2]
  exact ((Submodule.span_singleton_le_iff_mem (W i j) _).mpr (hsupport i j))
    (matrixSubmoduleTraceProjection_mem (ℂ ∙ W i j) X)

end ThomGame.Analysis
