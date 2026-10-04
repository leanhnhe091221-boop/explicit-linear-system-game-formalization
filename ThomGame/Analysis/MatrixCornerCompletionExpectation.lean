module

public import ThomGame.Analysis.MatrixCornerComplementAlgebra
public import ThomGame.Analysis.MatrixSubmoduleTraceProjection
public import ThomGame.Analysis.MatrixRectanglePairingCompression

/-!
# Exact expectation formula for the completed corner algebra

The actual trace expectation is the projection onto the supported
linear space plus the full complementary-corner compression.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixCornerCompletion_expectation (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hQS : Q ∈ S)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X) (X : CMatrix d) :
    matrixTraceProjection (matrixCornerCompletionAlgebra S Q hQ hQS hsupport) X =
      matrixSubmoduleTraceProjection S.toNonUnitalSubalgebra.toSubmodule X + (1 - Q) * X * (1 - Q) := by
  let P := matrixSubmoduleTraceProjection S.toNonUnitalSubalgebra.toSubmodule
  let R := 1 - Q
  have hR : IsStarProjection R := hQ.one_sub
  have hPX : P X ∈ S := matrixSubmoduleTraceProjection_mem S.toNonUnitalSubalgebra.toSubmodule X
  have hRX : R * (R * X * R) = R * X * R ∧ (R * X * R) * R = R * X * R := by
    constructor
    · rw [← mul_assoc R (R * X), ← mul_assoc R R X, hR.isIdempotentElem.eq]
    · rw [mul_assoc (R * X), hR.isIdempotentElem.eq]
  apply matrixTraceProjection_unique
  · exact (mem_matrixCornerCompletionAlgebra_iff S Q hQ hQS hsupport _).mpr
      ⟨P X, hPX, R * X * R, hRX, rfl⟩
  · intro B hB
    obtain ⟨C, hC, D, hD, rfl⟩ :=
      (mem_matrixCornerCompletionAlgebra_iff S Q hQ hQS hsupport B).mp hB
    change R * D = D ∧ D * R = D at hD
    have hCstar : star C * Q = star C := by
      simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star (hsupport C hC).1
    have hDstar : star D * R = star D := by
      simpa only [star_mul, hR.isSelfAdjoint.star_eq] using congrArg star hD.1
    have hCR := matrixComplementaryCorners_mul_zero Q (star C) (R * X * R) hCstar hRX.1
    have hDP := matrixComplementaryCorners_mul_zero R (star D) (P X) hDstar
      (by simpa only [R, sub_sub_cancel] using (hsupport (P X) hPX).1)
    have hCo := matrixSubmoduleTraceProjection_orthogonal S.toNonUnitalSubalgebra.toSubmodule X C hC
    have hDo := matrixRectangle_pairing_compress_right R R X D hR hR hD.1 hD.2
    change normalizedTrace (star (C + D) * (X - (P X + R * X * R))) = 0
    rw [star_add, add_mul, normalizedTrace_add]
    have hC0 : normalizedTrace (star C * (X - (P X + R * X * R))) = 0 := by
      rw [← sub_sub, mul_sub, hCR, normalizedTrace_sub, normalizedTrace_zero, sub_zero]
      exact hCo
    have hD0 : normalizedTrace (star D * (X - (P X + R * X * R))) = 0 := by
      rw [mul_sub, mul_add, hDP, zero_add, normalizedTrace_sub, hDo, sub_self]
    rw [hC0, hD0, add_zero]

end ThomGame.Analysis
