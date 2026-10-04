module

public import ThomGame.Analysis.MatrixResolventDissipation
public import ThomGame.Analysis.FiniteMatrixHilbert

/-!
# Off-diagonal commutator pairings

The real trace pairing of two skew-adjoint matrices can be restricted
to one column block when the first matrix is off diagonal. The resulting
bound has the absolute constant two, sufficient for ALT Lemma 3.2.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem abs_normalizedTrace_pairing_re_le [NeZero d] (C K : CMatrix d) :
    |(normalizedTrace (star C * K)).re| ≤ hsNorm C * hsNorm K := by
  apply (Complex.abs_re_le_norm _).trans
  simpa only [finiteMatrixHilbert_inner, finiteMatrixHilbert_norm] using!
    norm_inner_le_norm (𝕜 := ℂ) (finiteMatrixHilbertEquiv d C) (finiteMatrixHilbertEquiv d K)

theorem matrix_commutator_star {U F : CMatrix d} (hU : IsSelfAdjoint U) (hF : IsSelfAdjoint F) :
    star (U * F - F * U) = -(U * F - F * U) := by
  simp only [star_sub, star_mul, hU.star_eq, hF.star_eq]
  noncomm_ring

theorem matrix_projection_commutator_offDiagonal {U F : CMatrix d} (hF : F * F = F) :
    (U * F - F * U) * F + F * (U * F - F * U) = U * F - F * U := by
  calc
    _ = U * (F * F) - (F * F) * U := by noncomm_ring
    _ = _ := by rw [hF]

theorem normalizedTrace_skew_offDiagonal_pairing {C K F : CMatrix d}
    (hF : IsSelfAdjoint F) (hC : star C = -C) (hK : star K = -K)
    (hCF : C * F + F * C = C) :
    (normalizedTrace (star C * K)).re = 2 * (normalizedTrace (star C * (K * F))).re := by
  have hc : F * star C + star C * F = star C := by
    simpa only [star_add, star_mul, hF.star_eq] using congrArg star hCF
  have ha : normalizedTrace (F * star C * K) = normalizedTrace (star C * (K * F)) := by
    rw [mul_assoc F (star C) K, normalizedTrace_mul_comm F]
    simp only [mul_assoc]
  have hb : normalizedTrace (star C * F * K) = star (normalizedTrace (star C * (K * F))) := by
    rw [← normalizedTrace_star, star_mul, star_mul, star_star, hF.star_eq, hK, hC]
    calc
      _ = normalizedTrace ((-C) * (F * K)) := by simp only [mul_assoc]
      _ = normalizedTrace ((F * K) * (-C)) := normalizedTrace_mul_comm _ _
      _ = _ := by simp only [mul_neg, neg_mul, mul_assoc]
  have he : normalizedTrace (star C * K) =
      normalizedTrace (F * star C * K) + normalizedTrace (star C * F * K) := by
    rw [← normalizedTrace_add, ← add_mul, hc]
  rw [he, ha, hb, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

theorem abs_normalizedTrace_commutator_pairing_le [NeZero d] {U F D : CMatrix d}
    (hU : IsSelfAdjoint U) (hF : IsStarProjection F) (hD : IsSelfAdjoint D) :
    |(normalizedTrace (star (U * F - F * U) * (U * D - D * U))).re| ≤
      2 * hsNorm (U * F - F * U) * hsNorm ((U * D - D * U) * F) := by
  rw [normalizedTrace_skew_offDiagonal_pairing hF.isSelfAdjoint
    (matrix_commutator_star hU hF.isSelfAdjoint) (matrix_commutator_star hU hD)
    (matrix_projection_commutator_offDiagonal hF.isIdempotentElem.eq), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (abs_normalizedTrace_pairing_re_le (U * F - F * U) ((U * D - D * U) * F)) (by norm_num : (0 : ℝ) ≤ 2)

end ThomGame.Analysis
