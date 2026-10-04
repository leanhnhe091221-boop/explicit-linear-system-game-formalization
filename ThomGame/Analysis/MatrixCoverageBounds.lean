module

public import ThomGame.Analysis.MatrixCoverageDefect
public import ThomGame.Analysis.MatrixPositivePartTrace

/-!
# Coverage bounds before orthogonalization

The scalar coverage defect is bounded by the missing positive mass.
Trace subadditivity then compares a projection family with an actual
positive family whose sum is at most one. These are the final coverage
estimates used in ALT Lemma 3.3, without commutation assumptions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable def realCoverageResidual (t : ℝ) : ℝ := max (1 - Real.sqrt t) 0

theorem realCoverageResidual_continuous : Continuous realCoverageResidual := by
  unfold realCoverageResidual
  fun_prop

theorem realCoverageResidual_nonneg (t : ℝ) : 0 ≤ realCoverageResidual t := le_max_right _ _

theorem realCoverageResidual_le_one (t : ℝ) : realCoverageResidual t ≤ 1 :=
  max_le (by linarith [Real.sqrt_nonneg t]) zero_le_one

theorem realCoverageResidual_sq_le (t : ℝ) (ht : 0 ≤ t) :
    realCoverageResidual t ^ 2 ≤ max (1 - t) 0 := by
  by_cases ht1 : t ≤ 1
  · have hs : Real.sqrt t ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht1
    rw [realCoverageResidual, max_eq_left (sub_nonneg.mpr hs),
      max_eq_left (sub_nonneg.mpr ht1)]
    nlinarith [Real.sq_sqrt ht, mul_nonneg (Real.sqrt_nonneg t) (sub_nonneg.mpr hs)]
  · have hs : 1 ≤ Real.sqrt t := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_not_ge ht1)
    rw [realCoverageResidual, max_eq_right (sub_nonpos.mpr hs)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using le_max_right (1 - t) (0 : ℝ)

variable {d : Nat} {S : CMatrix d}

theorem matrix_one_sub_posPart_cfc (hS : IsSelfAdjoint S) (f : ℝ → ℝ)
    (hf : Continuous f) :
    (1 - cfc f S)⁺ = cfc (fun t => max (1 - f t) 0) S := by
  have he : cfc (fun t : ℝ => 1 - f t) S = 1 - cfc f S := by
    rw [cfc_sub (fun _ : ℝ => 1) f S continuous_const.continuousOn hf.continuousOn,
      cfc_const_one ℝ S hS]
  rw [matrix_posPart_eq_cfc, ← he]
  exact (cfc_comp' (fun t : ℝ => max t 0) (fun t => 1 - f t) S
    (by fun_prop) ((continuous_const.sub hf).continuousOn) hS).symm

theorem matrixCoverageResidual_eq_cfc (hS : 0 ≤ S) :
    matrixCoverageResidual S = cfc realCoverageResidual S := by
  rw [matrixCoverageResidual, matrix_sqrt_eq_cfc_real hS]
  exact matrix_one_sub_posPart_cfc hS.isSelfAdjoint Real.sqrt Real.continuous_sqrt

theorem matrixCoverageResidual_le_one (hS : 0 ≤ S) : matrixCoverageResidual S ≤ 1 := by
  rw [matrixCoverageResidual_eq_cfc hS]
  exact cfc_le_one realCoverageResidual S (fun _ _ => realCoverageResidual_le_one _)

theorem matrixCoverageResidual_sq_le_posPart (hS : 0 ≤ S) :
    matrixCoverageResidual S ^ 2 ≤ (1 - S)⁺ := by
  have hi : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hS.isSelfAdjoint
  have he : (1 - S)⁺ = cfc (fun t : ℝ => max (1 - t) 0) S := by
    simpa only [hi] using matrix_one_sub_posPart_cfc hS.isSelfAdjoint
      (fun t : ℝ => t) continuous_id
  rw [matrixCoverageResidual_eq_cfc hS, ← cfc_pow realCoverageResidual 2 S
    realCoverageResidual_continuous.continuousOn, he]
  exact cfc_mono (fun t ht => realCoverageResidual_sq_le t (spectrum_nonneg_of_nonneg hS ht))
    ((realCoverageResidual_continuous.pow 2).continuousOn) (by fun_prop)

theorem matrixCoverageDefect_le_posPart_trace (hS : 0 ≤ S) :
    matrixCoverageDefect S ≤ (normalizedTrace (1 - S)⁺).re :=
  normalizedTrace_re_mono (matrixCoverageResidual_sq_le_posPart hS)

theorem matrixCoverageDefect_le_one [NeZero d] (hS : 0 ≤ S) : matrixCoverageDefect S ≤ 1 := by
  have hb : matrixCoverageResidual S ^ 2 ≤ 1 := by
    rw [matrixCoverageResidual_eq_cfc hS, ← cfc_pow realCoverageResidual 2 S
      realCoverageResidual_continuous.continuousOn]
    apply cfc_le_one
    intro t _
    nlinarith [realCoverageResidual_nonneg t, realCoverageResidual_le_one t]
  simpa only [matrixCoverageDefect, normalizedTrace_one, Complex.one_re] using
    normalizedTrace_re_mono hb

theorem matrixFamilyCoverageDefect_comparison {ι : Type*} [Fintype ι]
    (D Q : ι → CMatrix d) (hD : ∀ i, IsSelfAdjoint (D i))
    (hQ : ∀ i, IsStarProjection (Q i)) (hD1 : (∑ i, D i) ≤ 1) :
    matrixFamilyCoverageDefect Q ≤ (normalizedTrace (1 - ∑ i, D i)).re +
      ∑ i, (normalizedTrace (D i - Q i)⁺).re := by
  have hDsum : IsSelfAdjoint (∑ i, D i) := isSelfAdjoint_sum _ (fun i _ => hD i)
  have hdiff : IsSelfAdjoint (∑ i, (D i - Q i)) :=
    isSelfAdjoint_sum _ (fun i _ => (hD i).sub (hQ i).isSelfAdjoint)
  have h1 : IsSelfAdjoint (1 : CMatrix d) := by simp [isSelfAdjoint_iff]
  have he : 1 - ∑ i, Q i = (1 - ∑ i, D i) + ∑ i, (D i - Q i) := by
    rw [Finset.sum_sub_distrib]
    abel
  have hp := normalizedTrace_posPart_add_le (h1.sub hDsum) hdiff
  have hsum := normalizedTrace_posPart_sum_le Finset.univ (fun i => D i - Q i)
    (fun i _ => (hD i).sub (hQ i).isSelfAdjoint)
  have hpos : (1 - ∑ i, D i)⁺ = 1 - ∑ i, D i :=
    (CFC.posPart_eq_self _).mpr (sub_nonneg.mpr hD1)
  calc
    _ ≤ (normalizedTrace (1 - ∑ i, Q i)⁺).re :=
      matrixCoverageDefect_le_posPart_trace (Finset.sum_nonneg fun i _ => (hQ i).nonneg)
    _ ≤ _ := by rw [he]; exact hp.trans (by rw [hpos]; exact add_le_add le_rfl hsum)

end ThomGame.Analysis
