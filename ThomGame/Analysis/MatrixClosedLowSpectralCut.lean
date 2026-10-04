module

public import ThomGame.Analysis.MatrixResolventSmallEnergyFamily

/-!
# The closed low spectral interval in ALT Lemma 3.3

The actual CFC projection for [0,gamma] dominates the complementary
upper cut on a positive matrix. This transports the stronger open-end
coverage bound to the exact interval appearing in the source.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat}

noncomputable def matrixClosedLowSpectralCut (A : CMatrix d) (s : ℝ) : CMatrix d :=
  cfc (fun t : ℝ => if 0 ≤ t ∧ t ≤ s then 1 else 0) A

theorem matrixClosedLowSpectralCut_isStarProjection (A : CMatrix d) (s : ℝ) :
    IsStarProjection (matrixClosedLowSpectralCut A s) := by
  constructor
  · show matrixClosedLowSpectralCut A s * matrixClosedLowSpectralCut A s = matrixClosedLowSpectralCut A s
    rw [matrixClosedLowSpectralCut, ← cfc_mul _ _ A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro t _
    dsimp only
    split_ifs <;> simp
  · exact IsSelfAdjoint.cfc

theorem matrix_spectral_complement_le_closedLow {A : CMatrix d} (hA : 0 ≤ A) (s : ℝ) :
    1 - matrixSpectralCut A s ≤ matrixClosedLowSpectralCut A s := by
  have he : cfc (fun t : ℝ => 1 - spectralStep s t) A = 1 - matrixSpectralCut A s := by
    rw [cfc_sub (fun _ : ℝ => 1) (spectralStep s) A continuous_const.continuousOn
      (A.finite_real_spectrum.continuousOn _), cfc_const_one ℝ A hA.isSelfAdjoint]
    rfl
  rw [← he, matrixClosedLowSpectralCut]
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hA ht
  by_cases hs : s ≤ t
  · simp only [spectralStep, ite_eq_left hs, sub_self, ht0, true_and]
    split_ifs <;> norm_num
  · simp [spectralStep, hs, ht0, (le_of_not_ge hs)]

theorem matrix_spectral_complement_trace_le_closedLow {A : CMatrix d} (hA : 0 ≤ A) (s : ℝ) :
    (normalizedTrace (1 - matrixSpectralCut A s)).re ≤ (normalizedTrace (matrixClosedLowSpectralCut A s)).re :=
  normalizedTrace_re_mono (matrix_spectral_complement_le_closedLow hA s)

theorem exists_matrixProjectionFamily_ALT_lemma3_3 [NeZero d] [NeZero h] {γ : ℝ} {e : CMatrix d}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (he : IsStarProjection e)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat)
    (htrace : (normalizedTrace (1 - e)).re + (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (henergy : matrixCoordinateEnergy U (1 - e) + (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) ≤ γ ^ 16) :
    ∃ Q : Fin n → CMatrix d,
      (∀ i, IsStarProjection (Q i) ∧ (Q i).rank ≤ (F i).rank) ∧
      (∑ i, matrixCoordinateEnergy U (Q i)) ≤ 100 * γ ^ 2 ∧
      (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum (1 - e) F i ^ 2 * Q i)).re) ≤ 3 * γ ∧
      matrixFamilyCoverageDefect Q ≤ (normalizedTrace (1 - e)).re +
        (normalizedTrace (matrixClosedLowSpectralCut (matrixProjectionPartialSum (1 - e) F n) γ)).re + 7 * γ := by
  obtain ⟨Q, hp, hq, hw, hc⟩ := exists_matrixProjectionFamily_small_energy_coverage hγ hγ4 he F hF U n htrace henergy
  have ht := matrix_spectral_complement_trace_le_closedLow
    (matrixProjectionPartialSum_nonneg he.one_sub.nonneg F hF n) γ
  exact ⟨Q, hp, hq, hw, hc.trans (add_le_add (add_le_add le_rfl ht) le_rfl)⟩

end ThomGame.Analysis
