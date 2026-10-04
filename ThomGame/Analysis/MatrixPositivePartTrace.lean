module

public import ThomGame.Analysis.MatrixSpectralCut

/-!
# Variational and subadditivity bounds for the trace of the positive part

The upper spectral cut attains the maximum trace pairing over positive
contractions. This proves trace subadditivity without any commutation
assumption, as needed in ALT Lemma 3.3.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {A B Q : CMatrix d}

theorem normalizedTrace_re_mono (hAB : A ≤ B) :
    (normalizedTrace A).re ≤ (normalizedTrace B).re := by
  have hp := (Complex.nonneg_iff.mp (normalizedTrace_nonneg (B - A) (sub_nonneg.mpr hAB))).1
  simpa only [normalizedTrace_sub, Complex.sub_re, sub_nonneg] using hp

theorem matrix_posPart_eq_cfc (A : CMatrix d) :
    A⁺ = cfc (fun t : ℝ => max t 0) A := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

theorem matrix_mul_spectralCut_zero (hA : Matrix.IsHermitian A) :
    A * matrixSpectralCut A 0 = A⁺ := by
  have hi : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  rw [matrix_posPart_eq_cfc, matrixSpectralCut]
  nth_rw 1 [← hi]
  rw [← cfc_mul (fun t : ℝ => t) (spectralStep 0) A continuous_id.continuousOn
    (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  by_cases ht : 0 ≤ t
  · simp [spectralStep, ht]
  · simp [spectralStep, ht, max_eq_right (le_of_not_ge ht)]

theorem normalizedTrace_mul_le_posPart (hA : IsSelfAdjoint A) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    (normalizedTrace (A * Q)).re ≤ (normalizedTrace A⁺).re := by
  have hp := (Complex.nonneg_iff.mp
    (normalizedTrace_mul_nonneg A⁺ (1 - Q) (CFC.posPart_nonneg A) (sub_nonneg.mpr hQ1))).1
  have hn := (Complex.nonneg_iff.mp
    (normalizedTrace_mul_nonneg A⁻ Q (CFC.negPart_nonneg A) hQ)).1
  have he : (normalizedTrace (A * Q)).re =
      (normalizedTrace (A⁺ * Q)).re - (normalizedTrace (A⁻ * Q)).re := by
    conv_lhs => rw [← CFC.posPart_sub_negPart A hA]
    rw [sub_mul, normalizedTrace_sub, Complex.sub_re]
  rw [mul_sub, mul_one, normalizedTrace_sub, Complex.sub_re] at hp
  linarith

theorem normalizedTrace_posPart_variational (hA : Matrix.IsHermitian A) :
    ∃ Q : CMatrix d, IsStarProjection Q ∧
      (normalizedTrace (A * Q)).re = (normalizedTrace A⁺).re ∧
      ∀ R : CMatrix d, 0 ≤ R → R ≤ 1 →
        (normalizedTrace (A * R)).re ≤ (normalizedTrace (A * Q)).re := by
  refine ⟨matrixSpectralCut A 0, matrixSpectralCut_isStarProjection hA 0, ?_, ?_⟩
  · rw [matrix_mul_spectralCut_zero hA]
  · intro R hR hR1
    rw [matrix_mul_spectralCut_zero hA]
    exact normalizedTrace_mul_le_posPart hA hR hR1

theorem normalizedTrace_posPart_add_le (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (normalizedTrace (A + B)⁺).re ≤ (normalizedTrace A⁺).re + (normalizedTrace B⁺).re := by
  obtain ⟨Q, hQ, he, _⟩ := normalizedTrace_posPart_variational (hA.add hB)
  have ha := normalizedTrace_mul_le_posPart hA hQ.nonneg hQ.le_one
  have hb := normalizedTrace_mul_le_posPart hB hQ.nonneg hQ.le_one
  rw [add_mul, normalizedTrace_add, Complex.add_re] at he
  linarith

theorem normalizedTrace_posPart_mono (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAB : A ≤ B) : (normalizedTrace A⁺).re ≤ (normalizedTrace B⁺).re := by
  obtain ⟨Q, hQ, he, _⟩ := normalizedTrace_posPart_variational hA
  have hp := (Complex.nonneg_iff.mp
    (normalizedTrace_mul_nonneg (B - A) Q (sub_nonneg.mpr hAB) hQ.nonneg)).1
  have hb := normalizedTrace_mul_le_posPart hB hQ.nonneg hQ.le_one
  rw [sub_mul, normalizedTrace_sub, Complex.sub_re] at hp
  linarith

theorem normalizedTrace_posPart_sum_le {ι : Type*} (s : Finset ι) (A : ι → CMatrix d)
    (hA : ∀ i ∈ s, IsSelfAdjoint (A i)) :
    (normalizedTrace (∑ i ∈ s, A i)⁺).re ≤ ∑ i ∈ s, (normalizedTrace (A i)⁺).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : IsSelfAdjoint (∑ j ∈ s, A j) := by
      change star (∑ j ∈ s, A j) = ∑ j ∈ s, A j
      rw [star_sum]
      exact Finset.sum_congr rfl fun j hj => (hA j (Finset.mem_insert_of_mem hj)).star_eq
    exact (normalizedTrace_posPart_add_le (hA i (Finset.mem_insert_self i s)) hs).trans
      (add_le_add le_rfl (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))))

end ThomGame.Analysis
