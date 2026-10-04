module

public import ThomGame.Quantum.MeasurementObservable
public import ThomGame.Quantum.IncidenceLoss

/-! Actual observables and state-dependent error identities for arbitrary strategies. -/

@[expose] public section
namespace ThomGame.Quantum.CommutingStrategy

variable {R C H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : CommutingStrategy R C (Fin 3 → ZMod 2) (ZMod 2) H)

noncomputable def aliceBit (r : R) (i : Fin 3) : H →L[ℂ] H :=
  (T.alice r).observable (fun a => a i)

noncomputable def bobBit (c : C) : H →L[ℂ] H := (T.bob c).observable id

theorem aliceBit_selfAdjoint (r : R) (i : Fin 3) : IsSelfAdjoint (T.aliceBit r i) :=
  (T.alice r).observable_selfAdjoint _

theorem bobBit_selfAdjoint (c : C) : IsSelfAdjoint (T.bobBit c) :=
  (T.bob c).observable_selfAdjoint _

theorem aliceBit_square (r : R) (i : Fin 3) : T.aliceBit r i * T.aliceBit r i = 1 :=
  (T.alice r).observable_square _

theorem bobBit_square (c : C) : T.bobBit c * T.bobBit c = 1 :=
  (T.bob c).observable_square _

theorem aliceBit_commute (r : R) (i j : Fin 3) : Commute (T.aliceBit r i) (T.aliceBit r j) :=
  (T.alice r).observable_commute _ _

theorem bit_cross_commute (r : R) (i : Fin 3) (c : C) : Commute (T.aliceBit r i) (T.bobBit c) :=
  (T.alice r).observable_cross_commute (T.bob c) (T.commute r c) _ _

theorem aliceBit_norm (r : R) (i : Fin 3) (ξ : H) : ‖T.aliceBit r i ξ‖ = ‖ξ‖ :=
  (T.alice r).observable_norm _ ξ

theorem bobBit_norm (c : C) (ξ : H) : ‖T.bobBit c ξ‖ = ‖ξ‖ :=
  (T.bob c).observable_norm _ ξ

theorem aliceBit_product (r : R) : T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2 =
    (T.alice r).observable (fun a => ∑ i, a i) := by
  simpa only [aliceBit, Fin.sum_univ_three] using (T.alice r).observable_triple
    (fun a => a 0) (fun a => a 1) (fun a => a 2)

theorem consistency_error_sq (r : R) (i : Fin 3) (c : C) :
    ‖T.aliceBit r i T.state - T.bobBit c T.state‖ ^ 2 =
      4 * ∑ a, ∑ b, if a i = b then 0 else T.correlation r c a b :=
  (T.alice r).observable_difference_norm_sq (T.bob c) (T.commute r c) _ _ T.state

theorem parity_error_sq (r : R) (c : C) (z : ZMod 2) :
    ‖(T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state - bitSign z • T.state‖ ^ 2 =
      4 * ∑ a, ∑ b, if (∑ i, a i) = z then 0 else T.correlation r c a b := by
  rw [T.aliceBit_product, (T.alice r).observable_sub_sign_norm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (∑ i, a i) = z
  · simp only [h, ite_true, Finset.sum_const_zero]
  · simp only [h, ite_false, T.alice_marginal]

variable [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] (S : SparseSystem R C)

theorem consistency_error_sq_le_loss (r : R) (i : Fin 3) :
    ‖T.aliceBit r i T.state - T.bobBit (S.column r i) T.state‖ ^ 2 ≤
      4 * (3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success T.correlation) := by
  rw [T.consistency_error_sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((S.inconsistency_le_rejection T.correlation T.isProbabilityTable r i).trans
      (S.rejection_le_loss T.correlation T.isProbabilityTable r i)) (by norm_num)

theorem parity_error_sq_le_loss (r : R) :
    ‖(T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state -
      bitSign (S.rhs r) • T.state‖ ^ 2 ≤
      4 * (3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success T.correlation) := by
  rw [T.parity_error_sq r (S.column r 0), mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((S.wrong_parity_le_rejection T.correlation T.isProbabilityTable r 0).trans
      (S.rejection_le_loss T.correlation T.isProbabilityTable r 0)) (by norm_num)

end ThomGame.Quantum.CommutingStrategy
