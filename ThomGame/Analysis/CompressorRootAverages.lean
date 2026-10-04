module

public import ThomGame.Analysis.CompressorPairDilation

/-! Symmetric averages of the actual finite compressor root words. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor FinitePrimeFivePair
variable {d r : ℕ} [NeZero d]

def compressorRootAction (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (α : Fin r → ZMod 5) :=
  matrixConjugationHilbertEquiv
    (Word.eval (fun s => f (FreeGroup.of s))
      (vectorWord (List.finRange r) (fun i => X root (σ i)) α))

def compressorRootAverage (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) :=
  finiteIsometrySymmetricAverage (compressorRootAction f root σ)

theorem compressorPairAction_left (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (α : Fin r → ZMod 5) :
    compressorPairAction f root σ (leftVector α) = compressorRootAction f root σ α := by
  unfold compressorPairAction compressorPairMatrices compressorRootAction
  rw [compressorPairCanonical_left, Word.map_eval]

theorem compressorPairAction_right (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (α : Fin r → ZMod 5) :
    compressorPairAction f root σ (rightVector α) = compressorRootAction f (right root) σ α := by
  unfold compressorPairAction compressorPairMatrices compressorRootAction
  rw [compressorPairCanonical_right, Word.map_eval]

theorem compressorRootAverage_norm (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (x : FiniteMatrixHilbert d) :
    ‖compressorRootAverage f root σ x‖ ≤ ‖x‖ :=
  finiteIsometrySymmetricAverage_norm_apply _ _

end ThomGame.Analysis
