module

public import ThomGame.Analysis.MatrixResolventDifferenceBounds

/-!
# Telescoping resolvent differences for projection families

Successive positive sums give an actual family of positive resolvent
differences. Their sum is a contraction and their weighted traces obey
ALT (3.6)--(3.7). The coverage comparison applies to any projection
family obtained from these differences.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {lam : ℝ}

noncomputable def matrixProjectionPartialSum (S₀ : CMatrix d) (F : Nat → CMatrix d) (n : Nat) :
    CMatrix d := S₀ + ∑ i ∈ Finset.range n, F i

@[simp] theorem matrixProjectionPartialSum_zero (S₀ : CMatrix d) (F : Nat → CMatrix d) :
    matrixProjectionPartialSum S₀ F 0 = S₀ := by simp [matrixProjectionPartialSum]

theorem matrixProjectionPartialSum_succ (S₀ : CMatrix d) (F : Nat → CMatrix d) (n : Nat) :
    matrixProjectionPartialSum S₀ F (n + 1) = matrixProjectionPartialSum S₀ F n + F n := by
  simp only [matrixProjectionPartialSum, Finset.sum_range_succ, add_assoc]

theorem matrixProjectionPartialSum_nonneg {S₀ : CMatrix d} (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat) :
    0 ≤ matrixProjectionPartialSum S₀ F n :=
  add_nonneg hS₀ (Finset.sum_nonneg fun i _ => (hF i).nonneg)

noncomputable def matrixResolventDifferenceFamily (lam : ℝ) (S₀ : CMatrix d)
    (F : Nat → CMatrix d) (i : Nat) : CMatrix d :=
  matrixProjectionResolventDifference lam (matrixProjectionPartialSum S₀ F i) (F i)

theorem matrixResolventDifferenceFamily_sum (lam : ℝ) (S₀ : CMatrix d)
    (F : Nat → CMatrix d) (n : Nat) :
    (∑ i ∈ Finset.range n, matrixResolventDifferenceFamily lam S₀ F i) =
      lam • (matrixPositiveResolvent lam S₀ -
        matrixPositiveResolvent lam (matrixProjectionPartialSum S₀ F n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, matrixResolventDifferenceFamily,
      matrixProjectionResolventDifference, ← matrixProjectionPartialSum_succ, ← smul_add]
    congr 1
    abel

theorem matrixResolventDifferenceFamily_nonneg (hlam : 0 < lam) {S₀ : CMatrix d}
    (hS₀ : 0 ≤ S₀) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (i : Nat) :
    0 ≤ matrixResolventDifferenceFamily lam S₀ F i :=
  matrixProjectionResolventDifference_nonneg hlam (matrixProjectionPartialSum_nonneg hS₀ F hF i) (hF i)

theorem matrixResolventDifferenceFamily_sum_le_one (hlam : 0 < lam) {S₀ : CMatrix d}
    (hS₀ : 0 ≤ S₀) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat) :
    (∑ i ∈ Finset.range n, matrixResolventDifferenceFamily lam S₀ F i) ≤ 1 := by
  rw [matrixResolventDifferenceFamily_sum]
  calc
    _ ≤ lam • matrixPositiveResolvent lam S₀ :=
      smul_le_smul_of_nonneg_left (sub_le_self _ (matrixPositiveResolvent_nonneg hlam
        (matrixProjectionPartialSum_nonneg hS₀ F hF n))) hlam.le
    _ ≤ 1 := by
      have he := smul_le_smul_of_nonneg_left (matrixPositiveResolvent_le_scalar hlam hS₀) hlam.le
      simpa only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] using he

theorem matrixResolventDifferenceFamily_weighted_trace_sum_le (hlam : 0 < lam) {S₀ : CMatrix d}
    (hS₀ : 0 ≤ S₀) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat) :
    (∑ i ∈ Finset.range n, (normalizedTrace (matrixProjectionPartialSum S₀ F i ^ 2 *
      matrixResolventDifferenceFamily lam S₀ F i)).re) ≤
      lam * ∑ i ∈ Finset.range n, (normalizedTrace (F i)).re := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => matrixProjectionResolventDifference_weighted_trace_le
    hlam (matrixProjectionPartialSum_nonneg hS₀ F hF i) (hF i)

theorem matrixResolventDifferenceFamily_coverage_bound (hlam : 0 < lam) {S₀ : CMatrix d}
    (hS₀ : 0 ≤ S₀) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (n : Nat) (Q : Fin n → CMatrix d) (hQ : ∀ i, IsStarProjection (Q i)) :
    matrixFamilyCoverageDefect Q ≤
      (normalizedTrace (1 - lam • matrixPositiveResolvent lam S₀)).re +
      (normalizedTrace (lam • matrixPositiveResolvent lam (matrixProjectionPartialSum S₀ F n))).re +
      ∑ i : Fin n, (normalizedTrace (matrixResolventDifferenceFamily lam S₀ F i - Q i)⁺).re := by
  have hsum : (∑ i : Fin n, matrixResolventDifferenceFamily lam S₀ F i) ≤ 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using matrixResolventDifferenceFamily_sum_le_one hlam hS₀ F hF n
  have hc := matrixFamilyCoverageDefect_comparison
    (fun i : Fin n => matrixResolventDifferenceFamily lam S₀ F i) Q
    (fun i => (matrixResolventDifferenceFamily_nonneg hlam hS₀ F hF i).isSelfAdjoint) hQ hsum
  have he : (normalizedTrace (1 - ∑ i : Fin n, matrixResolventDifferenceFamily lam S₀ F i)).re =
      (normalizedTrace (1 - lam • matrixPositiveResolvent lam S₀)).re +
      (normalizedTrace (lam • matrixPositiveResolvent lam (matrixProjectionPartialSum S₀ F n))).re := by
    rw [Fin.sum_univ_eq_sum_range, matrixResolventDifferenceFamily_sum, smul_sub,
      sub_sub_eq_add_sub, normalizedTrace_sub, normalizedTrace_add,
      normalizedTrace_sub, Complex.sub_re, Complex.add_re, Complex.sub_re]
    ring
  rwa [he] at hc

end ThomGame.Analysis
