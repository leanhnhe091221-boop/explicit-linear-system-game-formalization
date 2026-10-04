module

public import ThomGame.Analysis.MatrixPartitionUnitaryPair

/-!
# Doubled unitary tuples and the perturbation estimate in ALT Lemma 4.2

For any actual projection partition, the constructed pair of tuples
reduces every block, is the identity on the bad block, and averages to
the original compression on the other blocks. The total perturbation
has the original ambient normalized boundary-energy bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} [Fintype μ] {d h : Nat} [NeZero h]

theorem matrixCoordinateEnergy_partition_identity (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Fin h → UnitaryMatrix d) :
    4 * (∑ j, hsNorm ((U j).val - matrixBlockPinch E (U j).val) ^ 2) =
      8 * (h : ℝ) * ∑ i, matrixCoordinateEnergy U (E i) := by
  have hc : (∑ j, ∑ i, hsNorm ((U j).val * E i - E i * (U j).val) ^ 2) =
      2 * ∑ j, hsNorm ((U j).val - matrixBlockPinch E (U j).val) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [rectHSNorm_eq_hsNorm] using
      rectHSNorm_unitary_pinching_commutator_sum d E hE horth hsum (U j)
  have he : (∑ i, matrixCoordinateEnergy U (E i)) =
      lazyMarkovWeight h * (∑ j, ∑ i, hsNorm ((U j).val * E i - E i * (U j).val) ^ 2) := by
    simp only [matrixCoordinateEnergy, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he, hc]
  calc
    _ = 16 * (lazyMarkovWeight h * (h : ℝ)) *
        (∑ j, hsNorm ((U j).val - matrixBlockPinch E (U j).val) ^ 2) := by
      rw [lazyMarkovWeight_mul_card]
      ring
    _ = _ := by ring

theorem exists_matrixPartition_unitary_tuple (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Fin h → UnitaryMatrix d) (bad : μ) :
    ∃ V W : Fin h → UnitaryMatrix d,
      (∀ i j, Commute (E i) (V j).val) ∧ (∀ i j, Commute (E i) (W j).val) ∧
      (∀ j, E bad * (V j).val = E bad) ∧ (∀ j, E bad * (W j).val = E bad) ∧
      (∀ i, i ≠ bad → ∀ j,
        E i * (V j).val + E i * (W j).val = (2 : ℂ) • (E i * (U j).val * E i)) ∧
      (∑ j, (hsNorm ((V j).val - (U j).val) ^ 2 + hsNorm ((W j).val - (U j).val) ^ 2)) ≤
        8 * (h : ℝ) * (∑ i, matrixCoordinateEnergy U (E i)) + 8 * (h : ℝ) * matrixTraceReal d (E bad) := by
  choose V W hVc hWc hVb hWb havg hVe hWe using
    fun j => exists_matrixPartition_unitary_pair d E hE horth hsum (U j) bad
  refine ⟨V, W, (fun i j => hVc j i), (fun i j => hWc j i), hVb, hWb, (fun i hi j => havg j i hi), ?_⟩
  have hj (j : Fin h) : hsNorm ((V j).val - (U j).val) ^ 2 + hsNorm ((W j).val - (U j).val) ^ 2 ≤
      4 * hsNorm ((U j).val - matrixBlockPinch E (U j).val) ^ 2 + 8 * matrixTraceReal d (E bad) := by
    have hv := hVe j
    have hw := hWe j
    simp only [rectHSNorm_eq_hsNorm] at hv hw
    linarith only [hv, hw]
  have ht := Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht ⊢
  rw [matrixCoordinateEnergy_partition_identity E hE horth hsum U] at ht
  convert ht using 1
  ring

end ThomGame.Analysis
