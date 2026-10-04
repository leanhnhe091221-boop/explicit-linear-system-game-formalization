module

public import ThomGame.Analysis.MatrixUnitSpanSupport

/-!
# Completing a supported matrix algebra by its full complementary corner

This is the concrete algebra A0 + (1-Q) M_d (1-Q). Its underlying
submodule is exactly the sum of the two orthogonal corners.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

theorem matrixComplementaryCorners_mul_zero (Q X Y : CMatrix d)
    (hX : X * Q = X) (hY : (1 - Q) * Y = Y) : X * Y = 0 := by
  have hQY : Q * Y = 0 := by
    apply sub_eq_self.mp
    simpa only [sub_mul, one_mul] using hY
  calc
    X * Y = (X * Q) * Y := by rw [hX]
    _ = 0 := by rw [mul_assoc, hQY, mul_zero]

def matrixCornerNonUnitalAlgebra (Q : CMatrix d) (hQ : IsStarProjection Q) :
    NonUnitalStarSubalgebra ℂ (CMatrix d) :=
  { matrixRectangleSubmodule Q Q with
    mul_mem' := by
      intro X Y hX hY
      exact ⟨by rw [← mul_assoc, hX.1], by rw [mul_assoc, hY.2]⟩
    star_mem' := by
      intro X hX
      exact ⟨by simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hX.2,
        by simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hX.1⟩ }

def matrixCornerCompletionSubmodule (S : NonUnitalStarSubalgebra ℂ (CMatrix d)) (Q : CMatrix d) :
    Submodule ℂ (CMatrix d) :=
  S.toNonUnitalSubalgebra.toSubmodule ⊔ matrixRectangleSubmodule (1 - Q) (1 - Q)

def matrixCornerCompletionNonUnital (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X) : NonUnitalStarSubalgebra ℂ (CMatrix d) :=
  { matrixCornerCompletionSubmodule S Q with
    mul_mem' := by
      intro X Y hX hY
      obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hX
      obtain ⟨C, hC, D, hD, rfl⟩ := Submodule.mem_sup.mp hY
      have hAD := matrixComplementaryCorners_mul_zero Q A D (hsupport A hA).2 hD.1
      have hBC := matrixComplementaryCorners_mul_zero (1 - Q) B C hB.2
        (by simpa only [sub_sub_cancel] using (hsupport C hC).1)
      rw [add_mul, mul_add, mul_add, hAD, hBC, add_zero, zero_add]
      exact Submodule.mem_sup.mpr ⟨A * C, S.mul_mem hA hC, B * D,
        (matrixCornerNonUnitalAlgebra (1 - Q) hQ.one_sub).mul_mem hB hD, rfl⟩
    star_mem' := by
      intro X hX
      obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hX
      rw [star_add]
      exact Submodule.mem_sup.mpr ⟨star A, S.star_mem' hA, star B,
        (matrixCornerNonUnitalAlgebra (1 - Q) hQ.one_sub).star_mem' hB, rfl⟩ }

theorem matrixCornerCompletion_one_mem (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hQS : Q ∈ S)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X) :
    1 ∈ matrixCornerCompletionNonUnital S Q hQ hsupport := by
  exact Submodule.mem_sup.mpr ⟨Q, hQS, 1 - Q,
    ⟨hQ.one_sub.isIdempotentElem.eq, hQ.one_sub.isIdempotentElem.eq⟩, by abel⟩

def matrixCornerCompletionAlgebra (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hQS : Q ∈ S)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X) : StarSubalgebra ℂ (CMatrix d) :=
  (matrixCornerCompletionNonUnital S Q hQ hsupport).toStarSubalgebra
    (matrixCornerCompletion_one_mem S Q hQ hQS hsupport)

theorem mem_matrixCornerCompletionAlgebra_iff (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hQS : Q ∈ S)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X) (X : CMatrix d) :
    X ∈ matrixCornerCompletionAlgebra S Q hQ hQS hsupport ↔
      ∃ A ∈ S, ∃ B : CMatrix d, ((1 - Q) * B = B ∧ B * (1 - Q) = B) ∧ A + B = X :=
  Submodule.mem_sup

theorem matrixCornerCompletionAlgebra_mem_of_commute (S : NonUnitalStarSubalgebra ℂ (CMatrix d))
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hQS : Q ∈ S)
    (hsupport : ∀ X ∈ S, Q * X = X ∧ X * Q = X)
    (X : CMatrix d) (hcomm : Commute Q X) (hQX : Q * X ∈ S) :
    X ∈ matrixCornerCompletionAlgebra S Q hQ hQS hsupport := by
  let R := 1 - Q
  have hR : R * R = R := hQ.one_sub.isIdempotentElem.eq
  have hXR : X * R = R * X := by
    dsimp only [R]
    rw [mul_sub, mul_one, sub_mul, one_mul, hcomm.eq]
  apply (mem_matrixCornerCompletionAlgebra_iff S Q hQ hQS hsupport X).mpr
  refine ⟨Q * X, hQX, R * X, ⟨?_, ?_⟩, ?_⟩
  · change R * (R * X) = R * X
    rw [← mul_assoc, hR]
  · change (R * X) * R = R * X
    rw [mul_assoc, hXR, ← mul_assoc, hR]
  · dsimp only [R]
    rw [sub_mul, one_mul]
    abel

end ThomGame.Analysis
