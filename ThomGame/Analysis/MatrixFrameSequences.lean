module

public import ThomGame.Analysis.MatrixFrameStabilizationBounds
public import ThomGame.Analysis.BoundedMatrixSequences

/-!
# Frame lift and compression on actual bounded matrix sequences

Zero extension is linear, multiplicative and star preserving. Compression
is linear and recovers the source exactly. Both preserve uniform operator
bounds, so they are defined on the actual sequence algebras.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1)

noncomputable def matrixFrameSequenceLift : BoundedMatrixSequence dims →ₗ[ℂ] BoundedMatrixSequence large where
  toFun A := ⟨fun i => matrixFrameLift (F i) (A.val i), by
    obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
    exact ⟨K, hK, fun i => (matrixFrameLift_opNorm (F i) (hF i) (A.val i)).le.trans (hA i)⟩⟩
  map_add' A B := by
    apply Subtype.ext
    exact funext fun i => matrixFrameLift_add (F i) (A.val i) (B.val i)
  map_smul' c A := by
    apply Subtype.ext
    exact funext fun i => matrixFrameLift_smul (F i) c (A.val i)

noncomputable def matrixFrameSequenceCompression :
    BoundedMatrixSequence large →ₗ[ℂ] BoundedMatrixSequence dims where
  toFun A := ⟨fun i => (F i)ᴴ * A.val i * F i, by
    obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound large A
    exact ⟨K, hK, fun i => (matrixFrameCompression_opNorm_le (F i) (hF i) (A.val i)).trans (hA i)⟩⟩
  map_add' A B := by
    apply Subtype.ext
    funext i
    change (F i)ᴴ * (A.val i + B.val i) * F i = (F i)ᴴ * A.val i * F i + (F i)ᴴ * B.val i * F i
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    apply Subtype.ext
    funext i
    change (F i)ᴴ * (c • A.val i) * F i = c • ((F i)ᴴ * A.val i * F i)
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem matrixFrameSequenceLift_apply (A : BoundedMatrixSequence dims) (i : ι) :
    (matrixFrameSequenceLift dims large F hF A).val i = matrixFrameLift (F i) (A.val i) := rfl

@[simp] theorem matrixFrameSequenceCompression_apply (A : BoundedMatrixSequence large) (i : ι) :
    (matrixFrameSequenceCompression dims large F hF A).val i = (F i)ᴴ * A.val i * F i := rfl

theorem matrixFrameSequenceLift_mul (A B : BoundedMatrixSequence dims) :
    matrixFrameSequenceLift dims large F hF (A * B) =
      matrixFrameSequenceLift dims large F hF A * matrixFrameSequenceLift dims large F hF B := by
  apply Subtype.ext
  exact funext fun i => (matrixFrameLift_mul (hF i) (A.val i) (B.val i)).symm

theorem matrixFrameSequenceLift_star (A : BoundedMatrixSequence dims) :
    matrixFrameSequenceLift dims large F hF (star A) = star (matrixFrameSequenceLift dims large F hF A) := by
  apply Subtype.ext
  exact funext fun i => (matrixFrameLift_star (F i) (A.val i)).symm

theorem matrixFrameSequenceCompression_lift (A : BoundedMatrixSequence dims) :
    matrixFrameSequenceCompression dims large F hF (matrixFrameSequenceLift dims large F hF A) = A := by
  apply Subtype.ext
  exact funext fun i => matrixFrameCompression_lift (F i) (hF i) (A.val i)

theorem matrixFrameSequenceCompression_one :
    matrixFrameSequenceCompression dims large F hF 1 = 1 := by
  apply Subtype.ext
  funext i
  change (F i)ᴴ * 1 * F i = 1
  rw [Matrix.mul_one, hF i]

end ThomGame.Analysis
