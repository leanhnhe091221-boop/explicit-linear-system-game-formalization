module

public import ThomGame.Analysis.MatrixPolarCompletionDistance
public import ThomGame.Analysis.RectangularCompressionTraceLoss

/-!
# A unitary near the identity matching two large equal-rank projections

First correct the partial isometry P to a map from P onto Q, then
complete it to an ambient unitary. Only the small complement can change
freely. The distance bound keeps an arbitrary original normalization r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem rectHSNorm_sub_triangle {m : Nat} (r : Nat) (A B C : CMatrix m) :
    rectHSNorm r (A - C) ≤ rectHSNorm r (A - B) + rectHSNorm r (B - C) := by
  have h := rectHSNorm_add_le r (A - B) (B - C)
  rwa [sub_add_sub_cancel] at h

theorem rectHSNorm_sub_triangle_three {m : Nat} (r : Nat) (A B C D : CMatrix m) :
    rectHSNorm r (A - D) ≤ rectHSNorm r (A - B) + rectHSNorm r (B - C) + rectHSNorm r (C - D) := by
  calc
    rectHSNorm r (A - D) = rectHSNorm r ((A - B) + (B - C) + (C - D)) := by
      rw [sub_add_sub_cancel, sub_add_sub_cancel]
    _ ≤ rectHSNorm r ((A - B) + (B - C)) + rectHSNorm r (C - D) :=
      rectHSNorm_add_le r _ _
    _ ≤ rectHSNorm r (A - B) + rectHSNorm r (B - C) + rectHSNorm r (C - D) :=
      add_le_add (rectHSNorm_add_le r (A - B) (B - C)) le_rfl

theorem exists_matrixUnitary_projection_conjugacy_near {m : Nat} (r : Nat)
    {P Q : CMatrix m} (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hrank : P.rank = Q.rank) :
    ∃ U : UnitaryMatrix m, U.val * P * U.valᴴ = Q ∧
      rectHSNorm r (U.val - 1) ≤ 4 * Real.sqrt (matrixTraceReal r (1 - P)) := by
  have hPP : Pᴴ * P = P := by rw [hP.isSelfAdjoint.isHermitian.eq, hP.isIdempotentElem.eq]
  have hPP' : P * Pᴴ = P := by rw [hP.isSelfAdjoint.isHermitian.eq, hP.isIdempotentElem.eq]
  obtain ⟨V, hVi, hVf, hc⟩ := exists_matrixPartialIsometry_close_to_projection r
    (Y := P) (hPP.symm ▸ hP) hQ (by rw [hPP']; exact hrank.symm)
  rw [hPP] at hVi
  rw [hPP'] at hc
  have hvclose : rectHSNorm r (V - P) ≤ rectHSNorm r (P - Q) := by
    nlinarith [rectHSNorm_nonneg r (P - Q), rectHSNorm_nonneg r (V - P)]
  obtain ⟨U, hUi, hUf, hUV⟩ := exists_matrixPolar_completion
    (X := V) (P := (1 : CMatrix m)) (Q := (1 : CMatrix m))
    (IsStarProjection.one _) (IsStarProjection.one _) rfl (Matrix.mul_one V) (Matrix.one_mul V)
  have habs : matrixRectAbs V = P := by
    rw [matrixRectAbs_of_initial_projection (hVi.symm ▸ hP), hVi]
  rw [habs] at hUV
  let W : UnitaryMatrix m := ⟨U, hUi, hUf⟩
  have hUP : U * P = V := by
    rw [← hUV, ← Matrix.mul_assoc, hUf, Matrix.one_mul]
  have hconj : U * P * Uᴴ = Q := by
    calc
      _ = U * (P * P) * Uᴴ := by rw [hP.isIdempotentElem.eq]
      _ = (U * P) * (U * P)ᴴ := by simp only [Matrix.conjTranspose_mul, hP.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]
      _ = Q := by rw [hUP, hVf]
  have hpNorm : rectHSNorm r (1 - P) = Real.sqrt (matrixTraceReal r (1 - P)) := by
    rw [← rectHSNorm_projection_sq r hP.one_sub, Real.sqrt_sq (rectHSNorm_nonneg r _)]
  have hcrank : (1 - Q).rank = (1 - P).rank := by
    have hp := matrixProjection_rank_one_sub_add hP
    have hq := matrixProjection_rank_one_sub_add hQ
    omega
  have hqNorm : rectHSNorm r (1 - Q) = Real.sqrt (matrixTraceReal r (1 - P)) := by
    have he : matrixTraceReal r (1 - Q) = matrixTraceReal r (1 - P) := by
      rw [matrixTraceReal_projection_rank r hQ.one_sub, matrixTraceReal_projection_rank r hP.one_sub, hcrank]
    rw [← he, ← rectHSNorm_projection_sq r hQ.one_sub, Real.sqrt_sq (rectHSNorm_nonneg r _)]
  have hPQ : rectHSNorm r (P - Q) ≤ 2 * Real.sqrt (matrixTraceReal r (1 - P)) := by
    calc
      _ = rectHSNorm r ((P - 1) + (1 - Q)) := by congr 1; abel
      _ ≤ rectHSNorm r (P - 1) + rectHSNorm r (1 - Q) := rectHSNorm_add_le _ _ _
      _ = _ := by rw [rectHSNorm_sub_comm r P 1, hpNorm, hqNorm]; ring
  have hUVnorm : rectHSNorm r (U - V) = Real.sqrt (matrixTraceReal r (1 - P)) := by
    rw [show U - V = U * (1 - P) by rw [Matrix.mul_sub, Matrix.mul_one, hUP]]
    change rectHSNorm r (W.val * (1 - P)) = _
    rw [rectHSNorm_unitary_mul, hpNorm]
  have ht := rectHSNorm_sub_triangle_three r U V P 1
  rw [hUVnorm, rectHSNorm_sub_comm r P 1, hpNorm] at ht
  have hv := hvclose.trans hPQ
  have hb := ht.trans (add_le_add (add_le_add (le_refl (Real.sqrt (matrixTraceReal r (1 - P)))) hv)
    (le_refl (Real.sqrt (matrixTraceReal r (1 - P)))))
  have he : Real.sqrt (matrixTraceReal r (1 - P)) + 2 * Real.sqrt (matrixTraceReal r (1 - P)) +
      Real.sqrt (matrixTraceReal r (1 - P)) = 4 * Real.sqrt (matrixTraceReal r (1 - P)) := by ring
  rw [he] at hb
  exact ⟨W, hconj, hb⟩

end ThomGame.Analysis
