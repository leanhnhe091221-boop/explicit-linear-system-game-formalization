module

public import ThomGame.Analysis.MatrixALTProposition3_5
public import ThomGame.Analysis.MatrixFiniteResolventRounding

/-!
# Order and rank transfer for ALT's finite-family correction
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixClosedLowSpectralCut_mono (A : CMatrix d) {s t : ℝ} (hst : s ≤ t) :
    matrixClosedLowSpectralCut A s ≤ matrixClosedLowSpectralCut A t := by
  unfold matrixClosedLowSpectralCut
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro x _
  by_cases hs : 0 ≤ x ∧ x ≤ s
  · have ht : 0 ≤ x ∧ x ≤ t := ⟨hs.1, hs.2.trans hst⟩
    simp only [ite_eq_left hs, ite_eq_left ht, le_refl]
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

theorem matrixSubprojection_rank_le {P Q : CMatrix d}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P ≤ Q) : P.rank ≤ Q.rank := by
  calc
    P.rank = (P * Q).rank := congrArg Matrix.rank ((hP.le_iff_mul_eq_left hQ).mp hPQ).symm
    _ ≤ Q.rank := Matrix.rank_mul_le_right _ _

theorem matrixPartialIsometry_initial_rank_le {V Q : CMatrix d}
    (hV : IsStarProjection (Vᴴ * V)) (hQ : IsStarProjection Q) (hVQ : V * Vᴴ ≤ Q) :
    (Vᴴ * V).rank ≤ Q.rank := by
  have hf := matrixSubprojection_rank_le (matrixPartialIsometry_final_projection hV) hQ hVQ
  simpa only [Matrix.rank_conjTranspose_mul_self, Matrix.rank_self_mul_conjTranspose] using hf

end ThomGame.Analysis
