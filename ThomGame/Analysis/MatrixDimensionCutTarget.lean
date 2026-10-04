module

public import ThomGame.Analysis.MatrixDimensionCutHausdorff
public import ThomGame.Analysis.MatrixFrameMoveToCorner
public import ThomGame.Analysis.MatrixNestedFrameScalarAlgebra
public import ThomGame.Analysis.MatrixUnitaryConjugationDistance

/-!
# Actual algebras in the prescribed smaller dimension

The target is expressed in standard coordinates. Its retained frame is
the near-identity unitary image of the original algebraic cut.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {m d : Nat} {A : StarSubalgebra ℂ (CMatrix m)}
    (S : MatrixSubalgebraDimensionCut A d) (hd : d ≤ m)

structure MatrixDimensionCutTarget where
  unitary : UnitaryMatrix m
  frame : Matrix (Fin d) (Fin S.size) ℂ
  initial : frameᴴ * frame = 1
  place : matrixCanonicalCornerFrame hd * frame = unitary.val * S.frame
  near : rectHSNorm m (unitary.val - 1) ≤
    4 * Real.sqrt (matrixTraceReal m (1 - S.frame * S.frameᴴ))

theorem exists_matrixDimensionCutTarget : Nonempty (MatrixDimensionCutTarget S hd) := by
  obtain ⟨U, G, hG, he, hn⟩ := exists_matrixFrame_move_to_corner_near m S.frame S.initial
    (matrixCanonicalCornerFrame hd) (matrixCanonicalCornerFrame_initial hd)
    (matrixSubalgebraDimensionCut_size_le A d S)
  exact ⟨⟨U, G, hG, he, hn⟩⟩

namespace MatrixDimensionCutTarget

variable {S hd} (T : MatrixDimensionCutTarget S hd)

noncomputable def algebra : StarSubalgebra ℂ (CMatrix d) :=
  matrixFrameScalarAlgebra S.algebra T.frame T.initial

noncomputable def liftedAlgebra : StarSubalgebra ℂ (CMatrix m) :=
  matrixFrameScalarAlgebra T.algebra (matrixCanonicalCornerFrame hd) (matrixCanonicalCornerFrame_initial hd)

def fullFrame : Matrix (Fin m) (Fin S.size) ℂ := matrixCanonicalCornerFrame hd * T.frame

theorem fullFrame_initial : T.fullFrameᴴ * T.fullFrame = 1 :=
  matrixFrame_composition_initial _ _ (matrixCanonicalCornerFrame_initial hd) T.initial

theorem fullFrame_lift (X : CMatrix S.size) :
    matrixFrameLift T.fullFrame X = T.unitary.val * matrixFrameLift S.frame X * T.unitary.valᴴ := by
  change matrixFrameLift (matrixCanonicalCornerFrame hd * T.frame) X = _
  rw [T.place]
  simp only [matrixFrameLift, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem fullFrame_complement_trace (r : Nat) :
    matrixTraceReal r (1 - T.fullFrame * T.fullFrameᴴ) =
      matrixTraceReal r (1 - S.frame * S.frameᴴ) := by
  rw [matrixFrame_complement_trace r _ T.fullFrame_initial, matrixFrame_complement_trace r _ S.initial]

theorem fullFrame_lift_mem (X : CMatrix S.size) (hX : X ∈ S.algebra) :
    matrixFrameLift T.fullFrame X ∈ T.liftedAlgebra :=
  matrixNestedFrameScalar_lift_mem _ _ S.algebra (matrixCanonicalCornerFrame_initial hd) T.initial X hX

theorem fullFrame_compression_mem (Y : CMatrix m) (hY : Y ∈ T.liftedAlgebra) :
    T.fullFrameᴴ * Y * T.fullFrame ∈ S.algebra :=
  matrixNestedFrameScalar_compression_mem _ _ S.algebra (matrixCanonicalCornerFrame_initial hd) T.initial Y hY

theorem fullFrame_compression_loss (r : Nat) (Y : CMatrix m) (hn : matrixOpNorm Y ≤ 1) :
    rectHSNorm r (Y - matrixFrameLift T.fullFrame (T.fullFrameᴴ * Y * T.fullFrame)) ≤
      Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) := by
  rw [matrixFrameLift_compression]
  have h := rectHSNorm_projection_compression_loss r _ Y
    (matrixFrame_final_projection T.fullFrame T.fullFrame_initial) hn
  rwa [T.fullFrame_complement_trace] at h

end MatrixDimensionCutTarget
end ThomGame.Analysis
