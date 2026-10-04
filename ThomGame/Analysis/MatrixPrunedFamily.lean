module

public import ThomGame.Analysis.MatrixProjectionPruning
public import ThomGame.Analysis.MatrixReducingFamilyEnergy

/-!
# Finite-family pruning with the constants in ALT Lemma 4.2

Each block is actually pruned or discarded. The complement includes
the original bad block and all the removed parts. The trace and
energy bounds are summed with the original ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem exists_matrixPrunedFamily (U : Fin h → UnitaryMatrix d) (P : Option μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (hsum : ∑ i, P i = 1) (hred : ∀ i j, Commute (P i) (U j).val)
    {κ : ℝ} (hκ : 0 < κ) (ξ : μ → ℝ) (hξ : ∀ i, 0 ≤ ξ i)
    (hexpand : ∀ i (a : CMatrix d), IsStarProjection a → a ≤ P (some i) →
      2 * a.rank ≤ (P (some i)).rank → κ * matrixTraceReal d a - ξ i ≤ matrixCoordinateEnergy U a) :
    ∃ e : μ → CMatrix d, (∀ i, IsStarProjection (e i)) ∧ (∀ i, e i ≤ P (some i)) ∧
      Pairwise (fun i j => e i * e j = 0) ∧
      (∑ i, matrixCoordinateEnergy U (e i)) ≤ (∑ i, ξ i) / 8 ∧
      matrixTraceReal d (1 - ∑ i, e i) ≤ matrixTraceReal d (P none) + 16 * (∑ i, ξ i) / κ ∧
      ∀ i (p : CMatrix d), IsStarProjection p → p ≤ e i → 2 * p.rank ≤ (e i).rank →
        κ / 16 * matrixTraceReal d p ≤ matrixCompressedCoordinateEnergy U (e i) p := by
  classical
  choose e he hle henergy hmass hgap using fun i =>
    exists_matrixPrunedOrDiscardedProjection U (hP (some i)) (hred (some i)) hκ (hξ i) (hexpand i)
  have heorth : Pairwise (fun i j => e i * e j = 0) := by
    intro i j hij
    exact matrixProjection_subprojections_orthogonal (he i) (he j) (hP (some i)) (hP (some j))
      (hle i) (hle j) (horth (fun hh => hij (Option.some.inj hh)))
  refine ⟨e, he, hle, heorth, ?_, ?_, hgap⟩
  · calc
      _ ≤ ∑ i, ξ i / 8 := Finset.sum_le_sum fun i _ => henergy i
      _ = _ := (Finset.sum_div _ _ _).symm
  · have hmat : (1 : CMatrix d) - ∑ i, e i = P none + ∑ i, (P (some i) - e i) := by
      rw [← hsum, Fintype.sum_option, Finset.sum_sub_distrib]
      abel
    rw [hmat, matrixTraceReal_add, matrixTraceReal_sum]
    apply add_le_add_right
    calc
      _ ≤ ∑ i, 16 * ξ i / κ := Finset.sum_le_sum fun i _ => hmass i
      _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]

end ThomGame.Analysis
