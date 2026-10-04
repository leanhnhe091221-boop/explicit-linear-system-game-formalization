module

public import ThomGame.Analysis.MatrixPrunedFamily

/-!
# Pruning and actual doubled correction in ALT Lemma 4.2

The resulting actual partition and doubled unitary tuple have the
paper's trace, energy, and perturbation bounds and genuine projection
expansion in every retained corner. The passage from projection
expansion to scalar spectral gap is a separate Cheeger theorem.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] [NeZero h] {μ : Type*} [Fintype μ]

theorem exists_matrixPrunedDoubledExpansion (U : Fin h → UnitaryMatrix d) (P : Option μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (hsum : ∑ i, P i = 1) (hred : ∀ i j, Commute (P i) (U j).val)
    {κ : ℝ} (hκ : 0 < κ) (ξ : μ → ℝ) (hξ : ∀ i, 0 ≤ ξ i)
    (hexpand : ∀ i (a : CMatrix d), IsStarProjection a → a ≤ P (some i) →
      2 * a.rank ≤ (P (some i)).rank → κ * matrixTraceReal d a - ξ i ≤ matrixCoordinateEnergy U a) :
    ∃ E : Option μ → CMatrix d, ∃ T : Fin (h + h) → UnitaryMatrix d,
      (∀ i, IsStarProjection (E i)) ∧ Pairwise (fun i j => E i * E j = 0) ∧ (∑ i, E i = 1) ∧
      (∀ i, E (some i) ≤ P (some i)) ∧ (∀ i j, Commute (E i) (T j).val) ∧
      (∀ j, E none * (T j).val = E none) ∧
      (∑ i, matrixCoordinateEnergy U (E (some i))) ≤ (∑ i, ξ i) / 8 ∧
      matrixTraceReal d (E none) ≤ matrixTraceReal d (P none) + 16 * (∑ i, ξ i) / κ ∧
      (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
        2 * (h : ℝ) * (∑ i, ξ i) + 8 * (h : ℝ) * matrixTraceReal d (E none) ∧
      (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
        2 * (h : ℝ) * (∑ i, ξ i) + 8 * (h : ℝ) * matrixTraceReal d (P none) +
          128 * (h : ℝ) * (∑ i, ξ i) / κ ∧
      ∀ i (p : CMatrix d), IsStarProjection p → p ≤ E (some i) → 2 * p.rank ≤ (E (some i)).rank →
        κ / 16 * matrixTraceReal d p ≤ matrixCoordinateEnergy T p := by
  obtain ⟨e, he, hle, heorth, henergy, htrace, hgap⟩ :=
    exists_matrixPrunedFamily U P hP horth hsum hred hκ ξ hξ hexpand
  let E := matrixProjectionCompletion e
  have hE := matrixProjectionCompletion_isStarProjection e he heorth
  have hEorth := matrixProjectionCompletion_orthogonal e he heorth
  have hEsum := matrixProjectionCompletion_sum e
  obtain ⟨T, hTc, hTb, hdom, hdist⟩ := exists_matrixPartition_doubled_correction E hE hEorth hEsum U none
  have hPorth : Pairwise (fun i j => P (some i) * P (some j) = 0) := by
    intro i j hij
    exact horth (fun hh => hij (Option.some.inj hh))
  have htotal : (∑ i, matrixCoordinateEnergy U (E i)) = 2 * ∑ i, matrixCoordinateEnergy U (e i) :=
    matrixCoordinateEnergy_reducing_completion U (fun i => P (some i)) e
      (fun i => hP (some i)) he hle hPorth (fun i => hred (some i))
  have hdist' : (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
      2 * (h : ℝ) * (∑ i, ξ i) + 8 * (h : ℝ) * matrixTraceReal d (E none) := by
    rw [htotal] at hdist
    have hm := mul_le_mul_of_nonneg_left henergy (show (0 : ℝ) ≤ 16 * h by positivity)
    nlinarith only [hdist, hm]
  have hdist'' : (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
      2 * (h : ℝ) * (∑ i, ξ i) + 8 * (h : ℝ) * matrixTraceReal d (P none) +
        128 * (h : ℝ) * (∑ i, ξ i) / κ := by
    have hm := mul_le_mul_of_nonneg_left htrace (show (0 : ℝ) ≤ 8 * h by positivity)
    change _ ≤ 8 * (h : ℝ) * (matrixTraceReal d (P none) + 16 * (∑ i, ξ i) / κ) at hm
    change _ ≤ _ + 8 * (h : ℝ) * matrixTraceReal d (1 - ∑ i, e i) at hdist'
    calc
      _ ≤ 2 * (h : ℝ) * (∑ i, ξ i) +
          8 * (h : ℝ) * (matrixTraceReal d (P none) + 16 * (∑ i, ξ i) / κ) :=
        hdist'.trans (add_le_add_right hm _)
      _ = _ := by ring
  refine ⟨E, T, hE, hEorth, hEsum, hle, hTc, hTb, henergy, htrace, hdist', hdist'', ?_⟩
  intro i p hp hpi hhalf
  have hc := hdom (some i) (by simp) p
    ((hp.le_iff_mul_eq_right (he i)).mp hpi) ((hp.le_iff_mul_eq_left (he i)).mp hpi)
  exact (hgap i p hp hpi hhalf).trans hc

end ThomGame.Analysis
