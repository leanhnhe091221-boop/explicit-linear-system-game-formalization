module

public import ThomGame.Analysis.MatrixALTRefinement
public import ThomGame.Analysis.MatrixUltraproductALTPrunedDecomposition

/-!
# ALT Theorem 4.3 in the original matrix coordinates

Under the genuine ultraproduct spectral gap, every coordinate has an
actual projection partition reduced by an actual doubled unitary tuple.
Every nonzero block has scalar gap kappa squared over 2^28. The summed
squared perturbation tends to zero along the original ultrafilter.
Coordinates outside the construction set use the identity tuple and
an actual rank-one partition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem exists_matrixUltraproduct_ALT_decomposition (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k),
      ∃ Q : (k : Nat) → MatrixScalarGapPartition (T k) (κ ^ 2 / 2 ^ 28),
        (∀ k, (Q k).n ≤ 9 * dims k) ∧
        Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
          (L : Filter Nat) (𝓝 0) := by
  classical
  obtain ⟨η, _, _, _, hlim, hgood⟩ :=
    exists_matrixUltraproduct_ALT_prunedDecomposition dims U hd L hL κ hgap
  have hex (k : Nat) : ∃ T : Fin (h + h) → UnitaryMatrix (dims k),
      ∃ Q : MatrixScalarGapPartition T (κ ^ 2 / 2 ^ 28), Q.n ≤ 9 * dims k ∧
        (Nonempty (MatrixALTPrunedDecomposition (U k) κ (η k)) →
          (∑ j, hsNorm ((T j).val - (Fin.append (U k) (U k) j).val) ^ 2) ≤
            (h : ℝ) * altPrunedEditBound κ (η k)) := by
    let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
    by_cases hg : Nonempty (MatrixALTPrunedDecomposition (U k) κ (η k))
    · obtain ⟨pruned⟩ := hg
      obtain ⟨dec⟩ := exists_matrixALT_refinement (U k) pruned
      exact ⟨dec.T, dec.partition, dec.length_le, fun _ => dec.perturbation⟩
    · obtain ⟨Q, hQ⟩ := exists_matrixScalarGapPartition_identity (d := dims k) (h + h) (κ ^ 2 / 2 ^ 28)
      exact ⟨_, Q, by rw [hQ]; omega, fun hn => (hg hn).elim⟩
  choose T Q hn hbound using hex
  refine ⟨T, Q, hn, ?_⟩
  have hlim' : Tendsto (fun k => (h : ℝ) * altPrunedEditBound κ (η k)) (L : Filter Nat) (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (h : ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun k => Finset.sum_nonneg (fun j _ => sq_nonneg _))) _ hlim'
  filter_upwards [hgood] with k hk
  exact hbound k hk

theorem exists_matrixUltraproduct_ALT_theorem4_3 (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ (T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k)) (m : Nat → Nat)
      (E : (k : Nat) → Fin (m k) → CMatrix (dims k)),
      (∀ k, m k ≤ 9 * dims k) ∧
      (∀ k i, IsStarProjection (E k i)) ∧
      (∀ k, Pairwise (fun i j => E k i * E k j = 0)) ∧
      (∀ k, ∑ i, E k i = 1) ∧
      (∀ k i j, Commute (E k i) (T k j).val) ∧
      Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
        (L : Filter Nat) (𝓝 0) ∧
      ∀ k i, E k i ≠ 0 → ∀ X : CMatrix (dims k), E k i * X = X → X * E k i = X →
        κ ^ 2 / 2 ^ 28 * hsNorm (X - (normalizedTrace X / normalizedTrace (E k i)) • E k i) ^ 2 ≤
          matrixCoordinateEnergy (T k) X := by
  obtain ⟨T, Q, hn, hlim⟩ := exists_matrixUltraproduct_ALT_decomposition dims U hd L hL κ hgap
  exact ⟨T, fun k => (Q k).n, fun k => (Q k).E, hn,
    fun k => (Q k).projection, fun k => (Q k).orthogonal, fun k => (Q k).sum_one,
    fun k => (Q k).reducing, hlim, fun k => (Q k).scalar_gap⟩

end ThomGame.Analysis
