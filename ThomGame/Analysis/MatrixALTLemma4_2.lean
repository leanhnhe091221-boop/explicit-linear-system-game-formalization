module

public import ThomGame.Analysis.MatrixCornerCheeger
public import ThomGame.Analysis.MatrixPrunedDoubledExpansion

/-!
# ALT Lemma 4.2: actual expanding decomposition and scalar gap

Actual pruning and doubled unitary correction are followed by the
proved corner Cheeger inequality. The scalar gap is kappa squared
over 256, with all norms and traces in the original matrix algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] [NeZero h] {μ : Type*} [Fintype μ]

theorem exists_matrixPartition_ALT_lemma4_2 (U : Fin h → UnitaryMatrix d) (P : Option μ → CMatrix d)
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
      ∀ i, E (some i) ≠ 0 → ∀ X : CMatrix d, E (some i) * X = X → X * E (some i) = X →
        κ ^ 2 / 256 * hsNorm (X - (normalizedTrace X / normalizedTrace (E (some i))) • E (some i)) ^ 2 ≤
          matrixCoordinateEnergy T X := by
  obtain ⟨E, T, hE, hEorth, hEsum, hle, hTc, hTb, henergy, htrace, hdist, hdist', hgap⟩ :=
    exists_matrixPrunedDoubledExpansion U P hP horth hsum hred hκ ξ hξ hexpand
  refine ⟨E, T, hE, hEorth, hEsum, hle, hTc, hTb, henergy, htrace, hdist, hdist', ?_⟩
  intro i hi X hleft hright
  have hh := matrixCoordinateEnergy_corner_cheeger T (hE (some i)) hi (hTc (some i))
    (show 0 ≤ κ / 16 by positivity) (hgap i) X hleft hright
  convert hh using 1
  ring

end ThomGame.Analysis
