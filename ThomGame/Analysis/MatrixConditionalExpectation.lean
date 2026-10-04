module

public import ThomGame.Analysis.MatrixTraceProjection
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Conditional expectations in a matrix algebra

The trace orthogonal projection is positive, satisfies the Schwarz
inequality, and contracts the actual operator norm. All bounds are
independent of the matrix dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem normalizedTrace_nonneg (X : CMatrix d) (hX : 0 ≤ X) :
    0 ≤ normalizedTrace X := by
  exact div_nonneg (Matrix.nonneg_iff_posSemidef.mp hX).trace_nonneg (Nat.cast_nonneg d)

theorem normalizedTrace_mul_nonneg (X Y : CMatrix d) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ normalizedTrace (X * Y) := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY
  rw [← mul_assoc, normalizedTrace_mul_comm (X * star B) B, ← mul_assoc]
  exact normalizedTrace_nonneg _ (star_right_conjugate_nonneg hX B)

variable [NeZero d] (S : StarSubalgebra ℂ (CMatrix d))

theorem matrixTraceProjection_isSelfAdjoint (X : CMatrix d) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (matrixTraceProjection S X) := by
  change star (matrixTraceProjection S X) = matrixTraceProjection S X
  rw [← matrixTraceProjection_star, hX.star_eq]

theorem matrixTraceProjection_nonneg (X : CMatrix d) (hX : 0 ≤ X) :
    0 ≤ matrixTraceProjection S X := by
  let : IsClosed (S : Set (CMatrix d)) := S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  let Y := matrixTraceProjection S X
  have hY : IsSelfAdjoint Y := matrixTraceProjection_isSelfAdjoint S X hX.isSelfAdjoint
  have hn : Y⁻ ∈ S := cfcₙ_mem (𝕜' := ℂ) (·⁻ : ℝ → ℝ) (matrixTraceProjection_mem S X)
  have hns := (CFC.negPart_nonneg Y).isSelfAdjoint
  have hp := normalizedTrace_mul_nonneg Y⁻ X (CFC.negPart_nonneg Y) hX
  have heq := matrixTraceProjection_pairing S X Y⁻ hn
  rw [hns.star_eq] at heq
  rw [← heq] at hp
  have hmul : Y⁻ * Y = -(star Y⁻ * Y⁻) := by
    calc
      Y⁻ * Y = Y⁻ * (Y⁺ - Y⁻) := congrArg (Y⁻ * ·) (CFC.posPart_sub_negPart Y hY).symm
      _ = -(star Y⁻ * Y⁻) := by rw [mul_sub, CFC.negPart_mul_posPart, zero_sub, hns.star_eq]
  change 0 ≤ normalizedTrace (Y⁻ * Y) at hp
  rw [hmul, show -(star Y⁻ * Y⁻) = 0 - star Y⁻ * Y⁻ from (zero_sub _).symm,
    normalizedTrace_sub, normalizedTrace_zero, normalizedTrace_gram] at hp
  have hz : hsNorm Y⁻ ^ 2 = 0 := by
    have hr := (Complex.nonneg_iff.mp hp).1
    simp only [Complex.sub_re, Complex.zero_re, Complex.ofReal_re] at hr
    nlinarith [sq_nonneg (hsNorm Y⁻)]
  exact (CFC.negPart_eq_zero_iff Y hY).mp ((hsNorm_eq_zero_iff _).mp (sq_eq_zero_iff.mp hz))

noncomputable def matrixConditionalExpectation : CMatrix d →ₚ[ℂ] CMatrix d :=
  PositiveLinearMap.mk₀ (matrixTraceProjection S) (matrixTraceProjection_nonneg S)

@[simp] theorem matrixConditionalExpectation_apply (X : CMatrix d) :
    matrixConditionalExpectation S X = matrixTraceProjection S X := rfl

theorem matrixTraceProjection_schwarz (X : CMatrix d) :
    star (matrixTraceProjection S X) * matrixTraceProjection S X ≤
      matrixTraceProjection S (star X * X) := by
  have hp := matrixTraceProjection_nonneg S _ (star_mul_self_nonneg (X - matrixTraceProjection S X))
  have hm := matrixTraceProjection_mem S X
  rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
    matrixTraceProjection_mul_right S _ _ hm,
    matrixTraceProjection_mul_left S _ _ (S.star_mem' hm),
    matrixTraceProjection_eq_self S _ (S.mul_mem (S.star_mem' hm) hm),
    matrixTraceProjection_star] at hp
  simpa only [sub_self, sub_zero, sub_nonneg] using hp

theorem matrixTraceProjection_matrixOpNorm_le (X : CMatrix d) :
    matrixOpNorm (matrixTraceProjection S X) ≤ matrixOpNorm X := by
  have hp := (matrixConditionalExpectation S).norm_apply_le_of_nonneg
    (star X * X) (star_mul_self_nonneg X)
  simp only [matrixConditionalExpectation_apply, matrixTraceProjection_one, norm_one, one_mul] at hp
  have h := (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (matrixTraceProjection_schwarz S X) (star_mul_self_nonneg _)).trans hp
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa only [sq] using h)

end ThomGame.Analysis
