module

public import ThomGame.Quantum.IncidenceGame

/-! Every local error is controlled by the loss under actual incidence sampling. -/

@[expose] public section
namespace ThomGame.SparseSystem

open Quantum
open scoped BigOperators

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
  (S : SparseSystem R C)

noncomputable def rejection
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (r : R) (i : Fin 3) : ℝ :=
  ∑ a, ∑ b, if S.Accepts r i a b then 0 else p r (S.column r i) a b

omit [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] in
theorem rejection_nonneg
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (r : R) (i : Fin 3) : 0 ≤ S.rejection p r i := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split <;> first | exact le_rfl | exact hp.nonneg _ _ _ _

omit [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] in
theorem rejection_eq_one_sub
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (r : R) (i : Fin 3) : S.rejection p r i =
      1 - ∑ a, ∑ b, if S.Accepts r i a b then p r (S.column r i) a b else 0 := by
  rw [← hp.normalized r (S.column r i), ← Finset.sum_sub_distrib]
  unfold rejection
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp_all

theorem sum_rejection_eq_loss
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p) :
    (∑ r, ∑ i, S.rejection p r i) =
      (3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success p) := by
  simp only [S.rejection_eq_one_sub p hp, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [S.incidenceGame_success]
  have hR : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

theorem rejection_le_loss
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (r : R) (i : Fin 3) : S.rejection p r i ≤
      (3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success p) := by
  rw [← S.sum_rejection_eq_loss p hp]
  exact (Finset.single_le_sum (fun j _ => S.rejection_nonneg p hp r j) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun j _ => S.rejection_nonneg p hp s j))
      (Finset.mem_univ r))

omit [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] in
theorem inconsistency_le_rejection
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (r : R) (i : Fin 3) :
    (∑ a, ∑ b, if a i = b then 0 else p r (S.column r i) a b) ≤ S.rejection p r i := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases h : S.Accepts r i a b
  · simp only [h.2, h, ite_true, le_refl]
  · simp only [h, ite_false]
    split <;> first | exact hp.nonneg _ _ _ _ | exact le_rfl

omit [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] in
theorem wrong_parity_le_rejection
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (r : R) (i : Fin 3) :
    (∑ a, ∑ b, if (∑ j, a j) = S.rhs r then 0 else p r (S.column r i) a b) ≤
      S.rejection p r i := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases h : S.Accepts r i a b
  · simp only [h.1, h, ite_true, le_refl]
  · simp only [h, ite_false]
    split <;> first | exact hp.nonneg _ _ _ _ | exact le_rfl

end ThomGame.SparseSystem
