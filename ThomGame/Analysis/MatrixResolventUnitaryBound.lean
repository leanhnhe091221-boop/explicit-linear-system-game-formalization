module

public import ThomGame.Analysis.MatrixUnitaryDouble
public import ThomGame.Analysis.MatrixResolventSelfAdjointBound

/-!
# The full resolvent energy bound for arbitrary unitaries

The actual self-adjoint block dilation proves ALT Lemma 3.2, with
explicit dimension-free constant 292. Prepending an initial projection
also gives the version needed for the resolvent family in Lemma 3.3.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} [NeZero d]

theorem matrixResolvent_unitary_family_bound {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (U : UnitaryMatrix d) (n : Nat) :
    (∑ i ∈ Finset.range n, hsNorm ((U.val * matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i) -
      matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i) * U.val) * F i) ^ 2) ≤
      (292 / lam ^ 3) * (∑ i ∈ Finset.range n, hsNorm (U.val * F i - F i * U.val) ^ 2) := by
  have he := matrixResolvent_selfAdjoint_family_bound hlam hlam1
    (fun i => matrixDiagonalDouble d (F i)) (fun i => matrixDiagonalDouble_projection d (hF i))
    (matrixUnitaryDouble U) (matrixUnitaryDouble_isSelfAdjoint U) (matrixUnitaryDouble_mul_self U) n
  have hR (i : Nat) : matrixPositiveResolvent lam
      (matrixProjectionPartialSum 0 (fun i => matrixDiagonalDouble d (F i)) i) =
      matrixDiagonalDouble d (matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i)) := by
    rw [matrixDiagonalDouble_partial_sum, matrixDiagonalDouble_resolvent d hlam
      (matrixProjectionPartialSum_nonneg (le_refl 0) F hF i)]
  simp_rw [hR, matrixUnitaryDouble_commutator_hsNorm_sq] at he
  have hl := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    matrixUnitaryDouble_commutator_column_lower U (matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i)) (F i))
  rw [← Finset.mul_sum] at hl
  exact hl.trans ((mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

omit [NeZero d] in
noncomputable def matrixProjectionPrepend (P : CMatrix d) (F : Nat → CMatrix d) : Nat → CMatrix d
  | 0 => P
  | i + 1 => F i

omit [NeZero d] in
theorem matrixProjectionPrepend_partial_sum (P : CMatrix d) (F : Nat → CMatrix d) (n : Nat) :
    matrixProjectionPartialSum 0 (matrixProjectionPrepend P F) (n + 1) =
      matrixProjectionPartialSum P F n := by
  simp only [matrixProjectionPartialSum, zero_add, Finset.sum_range_succ', matrixProjectionPrepend]
  exact add_comm _ _

theorem matrixResolvent_unitary_family_bound_initial {lam : ℝ} {P : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : UnitaryMatrix d) (n : Nat) :
    (∑ i ∈ Finset.range n, hsNorm ((U.val * matrixPositiveResolvent lam (matrixProjectionPartialSum P F i) -
      matrixPositiveResolvent lam (matrixProjectionPartialSum P F i) * U.val) * F i) ^ 2) ≤
      (292 / lam ^ 3) * (hsNorm (U.val * P - P * U.val) ^ 2 +
        ∑ i ∈ Finset.range n, hsNorm (U.val * F i - F i * U.val) ^ 2) := by
  have hG (i : Nat) : IsStarProjection (matrixProjectionPrepend P F i) := by
    cases i with
    | zero => exact hP
    | succ i => exact hF i
  have he := matrixResolvent_unitary_family_bound hlam hlam1 (matrixProjectionPrepend P F) hG U (n + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at he
  simp only [matrixProjectionPrepend_partial_sum, matrixProjectionPrepend, matrixProjectionPartialSum_zero] at he
  rw [add_comm (∑ i ∈ Finset.range n, hsNorm (U.val * F i - F i * U.val) ^ 2)] at he
  exact (le_add_of_nonneg_right (sq_nonneg _)).trans he

end ThomGame.Analysis
