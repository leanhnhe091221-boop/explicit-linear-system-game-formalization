module

public import ThomGame.Analysis.MatrixFunctionalCalculusEnergy
public import ThomGame.Analysis.MatrixProjectionDistance
public import ThomGame.Analysis.MatrixRandomSignSums

/-!
# The one-sided coverage defect of a projection family

The residual is the actual positive part of one minus the positive
square root of the sum. Its squared normalized trace is zero exactly
when the sum dominates one. For orthogonal projections it equals the
trace of the complement, as in ALT Definition 3.1.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

noncomputable def matrixCoverageResidual (S : CMatrix d) : CMatrix d := (1 - CFC.sqrt S)⁺

noncomputable def matrixCoverageDefect (S : CMatrix d) : ℝ :=
  (normalizedTrace (matrixCoverageResidual S ^ 2)).re

noncomputable def matrixFamilyCoverageDefect {ι : Type*} [Fintype ι]
    (P : ι → CMatrix d) : ℝ := matrixCoverageDefect (∑ i, P i)

theorem matrixCoverageResidual_nonneg (S : CMatrix d) : 0 ≤ matrixCoverageResidual S :=
  CFC.posPart_nonneg _

theorem matrixCoverageResidual_isSelfAdjoint (S : CMatrix d) :
    IsSelfAdjoint (matrixCoverageResidual S) := (matrixCoverageResidual_nonneg S).isSelfAdjoint

theorem matrixCoverageDefect_eq_hsNorm_sq (S : CMatrix d) :
    matrixCoverageDefect S = hsNorm (matrixCoverageResidual S) ^ 2 := by
  have he := congrArg Complex.re (normalizedTrace_gram (matrixCoverageResidual S))
  simpa only [matrixCoverageDefect, sq, (matrixCoverageResidual_isSelfAdjoint S).star_eq,
    Complex.ofReal_re] using he

theorem matrixCoverageDefect_nonneg (S : CMatrix d) : 0 ≤ matrixCoverageDefect S := by
  rw [matrixCoverageDefect_eq_hsNorm_sq]
  exact sq_nonneg _

theorem matrix_sqrt_eq_cfc_real {S : CMatrix d} (hS : 0 ≤ S) :
    CFC.sqrt S = cfc Real.sqrt S := by
  rw [CFC.sqrt_eq_real_sqrt S hS, cfcₙ_eq_cfc]

theorem matrix_one_le_sqrt_iff {S : CMatrix d} (hS : 0 ≤ S) :
    1 ≤ CFC.sqrt S ↔ 1 ≤ S := by
  rw [matrix_sqrt_eq_cfc_real hS,
    one_le_cfc_iff Real.sqrt S Real.continuous_sqrt.continuousOn hS.isSelfAdjoint,
    CFC.one_le_iff (R := ℝ) S hS.isSelfAdjoint]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  have ht0 := spectrum_nonneg_of_nonneg hS ht
  simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt_iff ht0 (x := 1))

theorem matrixCoverageResidual_eq_zero_iff {S : CMatrix d} (hS : 0 ≤ S) :
    matrixCoverageResidual S = 0 ↔ 1 ≤ S := by
  have h1 : IsSelfAdjoint (1 : CMatrix d) := by simp [isSelfAdjoint_iff]
  rw [matrixCoverageResidual, CFC.posPart_eq_zero_iff _
    (h1.sub (CFC.sqrt_nonneg S).isSelfAdjoint), sub_nonpos,
    matrix_one_le_sqrt_iff hS]

theorem matrixCoverageDefect_eq_zero_iff [NeZero d] {S : CMatrix d} (hS : 0 ≤ S) :
    matrixCoverageDefect S = 0 ↔ 1 ≤ S := by
  rw [matrixCoverageDefect_eq_hsNorm_sq, sq_eq_zero_iff, hsNorm_eq_zero_iff,
    matrixCoverageResidual_eq_zero_iff hS]

theorem matrix_sqrt_projection {P : CMatrix d} (hP : IsStarProjection P) :
    CFC.sqrt P = P := CFC.sqrt_unique hP.isIdempotentElem.eq hP.nonneg

theorem matrixCoverageResidual_projection {P : CMatrix d} (hP : IsStarProjection P) :
    matrixCoverageResidual P = 1 - P := by
  rw [matrixCoverageResidual, matrix_sqrt_projection hP]
  exact (CFC.posPart_eq_self _).mpr hP.one_sub_nonneg

theorem matrixCoverageDefect_projection {P : CMatrix d} (hP : IsStarProjection P) :
    matrixCoverageDefect P = (normalizedTrace (1 - P)).re := by
  rw [matrixCoverageDefect_eq_hsNorm_sq, matrixCoverageResidual_projection hP]
  exact hsNorm_projection_sq hP.one_sub

theorem matrixFamilyCoverageDefect_nonneg {ι : Type*} [Fintype ι] (P : ι → CMatrix d) :
    0 ≤ matrixFamilyCoverageDefect P := matrixCoverageDefect_nonneg _

theorem matrixFamilyCoverageDefect_eq_zero_iff [NeZero d] {ι : Type*} [Fintype ι]
    (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i)) :
    matrixFamilyCoverageDefect P = 0 ↔ 1 ≤ ∑ i, P i :=
  matrixCoverageDefect_eq_zero_iff (Finset.sum_nonneg fun i _ => (hP i).nonneg)

theorem matrixFamilyCoverageDefect_orthogonal {ι : Type*} [Fintype ι]
    (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    matrixFamilyCoverageDefect P = (normalizedTrace (1 - ∑ i, P i)).re :=
  matrixCoverageDefect_projection (matrixOrthogonalSum_projection P hP horth)

end ThomGame.Analysis
