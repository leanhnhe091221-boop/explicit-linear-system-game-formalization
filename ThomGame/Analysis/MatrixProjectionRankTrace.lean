module

public import ThomGame.Analysis.MatrixPositivePartTrace

/-!
# Rank and normalized trace of matrix projections

Hermitian rank counts the nonzero eigenvalues. A projection has only
zero and one as eigenvalues, so its normalized trace is rank divided
by the original dimension. The formulas also cover zero dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {A P Q : CMatrix d}

theorem matrix_rank_eq_nonzero_eigenvalue_sum (hA : Matrix.IsHermitian A) :
    (A.rank : ℝ) = ∑ i, if hA.eigenvalues i = 0 then (0 : ℝ) else 1 := by
  classical
  rw [hA.rank_eq_card_non_zero_eigs]
  simp [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, ite_not]

theorem matrixProjection_eigenvalue_zero_or_one (hP : IsStarProjection P) (i : Fin d) :
    hP.isSelfAdjoint.isHermitian.eigenvalues i = 0 ∨
      hP.isSelfAdjoint.isHermitian.eigenvalues i = 1 := by
  have he := hP.isIdempotentElem.spectrum_subset ℝ
    (hP.isSelfAdjoint.isHermitian.eigenvalues_mem_spectrum_real i)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he

theorem matrixProjection_trace_eq_rank (hP : IsStarProjection P) :
    (normalizedTrace P).re = (P.rank : ℝ) / d := by
  rw [normalizedTrace_eq_eigenvalue_sum hP.isSelfAdjoint.isHermitian,
    matrix_rank_eq_nonzero_eigenvalue_sum hP.isSelfAdjoint.isHermitian]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases matrixProjection_eigenvalue_zero_or_one hP i with hi | hi <;> simp [hi]

theorem matrixProjection_rank_trace_mono (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hrank : P.rank ≤ Q.rank) : (normalizedTrace P).re ≤ (normalizedTrace Q).re := by
  rw [matrixProjection_trace_eq_rank hP, matrixProjection_trace_eq_rank hQ]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hrank) (Nat.cast_nonneg d)

theorem matrix_cfc_trace (hA : Matrix.IsHermitian A) (f : ℝ → ℝ) :
    (normalizedTrace (cfc f A)).re = (∑ i, f (hA.eigenvalues i)) / d := by
  rw [matrix_cfc_conjugate hA, matrixUnitaryConjugation_trace, normalizedTrace_diagonal_real]

theorem matrix_cfc_rank (hA : Matrix.IsHermitian A) (f : ℝ → ℝ) :
    (cfc f A).rank = Fintype.card {i // f (hA.eigenvalues i) ≠ 0} := by
  classical
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -Unitary.coe_star, Matrix.rank_diagonal, Function.comp_def]

theorem matrix_cfc_rank_le (hA : Matrix.IsHermitian A) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f A).rank ≤ A.rank := by
  rw [matrix_cfc_rank hA, hA.rank_eq_card_non_zero_eigs]
  apply Fintype.card_subtype_mono
  intro i hi he
  exact hi (by rw [he, hf])

theorem matrixSpectralCut_rank_le (hA : Matrix.IsHermitian A) {s : ℝ} (hs : 0 < s) :
    (matrixSpectralCut A s).rank ≤ A.rank := by
  apply matrix_cfc_rank_le hA (spectralStep s)
  simp [spectralStep, not_le.mpr hs]

end ThomGame.Analysis
