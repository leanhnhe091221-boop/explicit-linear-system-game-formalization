module

public import ThomGame.Analysis.MatrixFrameCompression

/-!
# Two actual corner unitaries averaging a compressed unitary

The construction takes place on the genuine range frame of q and is
transported back to the original matrix algebra. It also covers q = 0.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_matrixCorner_unitary_pair (r : Nat) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) (U : Matrix.unitaryGroup ι ℂ) :
    ∃ V W : Matrix ι ι ℂ,
      Vᴴ * V = q ∧ V * Vᴴ = q ∧ Wᴴ * W = q ∧ W * Wᴴ = q ∧
      V + W = (2 : ℂ) • (q * U.val * q) ∧
      rectHSNorm r (V - q * U.val * q) ^ 2 =
        matrixTraceReal r (q - (q * U.val * q)ᴴ * (q * U.val * q)) ∧
      rectHSNorm r (W - q * U.val * q) ^ 2 =
        matrixTraceReal r (q - (q * U.val * q)ᴴ * (q * U.val * q)) := by
  classical
  let κ := {i // hq.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0}
  let F : Matrix ι κ ℂ := matrixProjectionFrame hq
  have hFi : Fᴴ * F = 1 := matrixProjectionFrame_initial hq
  have hFf : F * Fᴴ = q := matrixProjectionFrame_final hq
  let B := Fᴴ * U.val * F
  obtain ⟨v, w, hmean, hvd, hwd⟩ := exists_matrixContraction_unitary_pair r
    (matrixFrameCompression_gram_le_one hq hFi hFf U)
  have hB : matrixFrameLift F B = q * U.val * q := by
    rw [matrixFrameLift_compression, hFf]
  have hgrams (T : Matrix.unitaryGroup κ ℂ) :
      (matrixFrameLift F T.val)ᴴ * matrixFrameLift F T.val = q ∧
      matrixFrameLift F T.val * (matrixFrameLift F T.val)ᴴ = q := by
    have hi : T.valᴴ * T.val = 1 := T.prop.1
    have hf : T.val * T.valᴴ = 1 := T.prop.2
    constructor
    · rw [matrixFrameLift_star, matrixFrameLift_mul hFi, hi, matrixFrameLift_one, hFf]
    · rw [matrixFrameLift_star, matrixFrameLift_mul hFi, hf, matrixFrameLift_one, hFf]
  have htr : matrixTraceReal r (1 - Bᴴ * B) =
      matrixTraceReal r (q - (q * U.val * q)ᴴ * (q * U.val * q)) := by
    rw [← matrixFrameLift_trace r hFi (1 - Bᴴ * B), matrixFrameLift_sub, matrixFrameLift_one, hFf,
      ← matrixFrameLift_mul hFi, ← matrixFrameLift_star, hB]
  have hdist (T : Matrix.unitaryGroup κ ℂ) :
      rectHSNorm r (matrixFrameLift F T.val - q * U.val * q) = rectHSNorm r (T.val - B) := by
    rw [← hB, ← matrixFrameLift_sub, matrixFrameLift_hsNorm r hFi]
  refine ⟨matrixFrameLift F v.val, matrixFrameLift F w.val,
    (hgrams v).1, (hgrams v).2, (hgrams w).1, (hgrams w).2, ?_, ?_, ?_⟩
  · rw [← matrixFrameLift_add, hmean, matrixFrameLift_smul, hB]
  · rw [hdist]
    exact hvd.trans htr
  · rw [hdist]
    exact hwd.trans htr

end ThomGame.Analysis
