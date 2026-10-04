module

public import ThomGame.Quantum.GameValue
public import ThomGame.Finite.RowOrdering
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! Uniform incidence sampling and the actual three-bit linear-system game. -/

@[expose] public section
namespace ThomGame.SparseSystem

open scoped BigOperators
open Quantum

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
  (S : SparseSystem R C)

omit [Fintype R] [Nonempty R] in
theorem sum_rowSupport (r : R) (f : C → ℝ) :
    (∑ c, if c ∈ S.rowSupport r then f c else 0) = ∑ i, f (S.column r i) := by
  have hs : Finset.univ.filter (fun c => c ∈ S.rowSupport r) = S.rowSupport r := by
    ext c
    simp
  rw [← Finset.sum_filter, hs, rowSupport, Finset.sum_image]
  intro i _ j _ hij
  exact S.column_injective r hij

noncomputable def incidenceWeight (r : R) (c : C) : ℝ :=
  if c ∈ S.rowSupport r then (3 * (Fintype.card R : ℝ))⁻¹ else 0

omit [Fintype C] in
theorem incidenceWeight_nonneg (r : R) (c : C) : 0 ≤ S.incidenceWeight r c := by
  unfold incidenceWeight
  split <;> positivity

theorem incidenceWeight_sum : ∑ r, ∑ c, S.incidenceWeight r c = 1 := by
  have hR : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [incidenceWeight, S.sum_rowSupport]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

instance acceptsDecidable (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    Decidable (S.Accepts r i a b) := by
  unfold Accepts
  infer_instance

noncomputable def incidencePayoff (r : R) (c : C) (a : Fin 3 → ZMod 2) (b : ZMod 2) : ℝ := by
  classical
  exact if ∃ i, S.column r i = c ∧ S.Accepts r i a b then 1 else 0

omit [Fintype R] [Nonempty R] [Fintype C] in
theorem incidencePayoff_nonneg (r : R) (c : C) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    0 ≤ S.incidencePayoff r c a b := by
  unfold incidencePayoff
  split <;> norm_num

omit [Fintype R] [Nonempty R] [Fintype C] in
theorem incidencePayoff_le_one (r : R) (c : C) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    S.incidencePayoff r c a b ≤ 1 := by
  unfold incidencePayoff
  split <;> norm_num

noncomputable def incidenceGame : FiniteGame R C (Fin 3 → ZMod 2) (ZMod 2) where
  weight := S.incidenceWeight
  weight_nonneg := S.incidenceWeight_nonneg
  weight_sum := S.incidenceWeight_sum
  payoff := S.incidencePayoff
  payoff_nonneg := S.incidencePayoff_nonneg
  payoff_le_one := S.incidencePayoff_le_one

theorem incidenceGame_weight (r : R) (i : Fin 3) :
    S.incidenceGame.weight r (S.column r i) = 1 / (3 * (Fintype.card R : ℝ)) := by
  have hi : S.column r i ∈ S.rowSupport r := (S.mem_rowSupport r _).mpr ⟨i, rfl⟩
  simp [incidenceGame, incidenceWeight, hi, one_div]

theorem incidenceGame_payoff (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    S.incidenceGame.payoff r (S.column r i) a b = 1 ↔ S.Accepts r i a b := by
  simp [incidenceGame, incidencePayoff, (S.column_injective r).eq_iff]

theorem incidenceGame_success (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) :
    S.incidenceGame.success p = (3 * (Fintype.card R : ℝ))⁻¹ *
      ∑ r, ∑ i, ∑ a, ∑ b, (if S.Accepts r i a b then p r (S.column r i) a b else 0) := by
  classical
  unfold FiniteGame.success
  change (∑ r, ∑ c, (if c ∈ S.rowSupport r then (3 * (Fintype.card R : ℝ))⁻¹ else 0) *
    S.incidenceGame.answerScore p r c) = _
  simp only [ite_mul, zero_mul, S.sum_rowSupport]
  simp only [FiniteGame.answerScore, incidenceGame, incidencePayoff,
    (S.column_injective _).eq_iff]
  simp only [exists_eq_left, ite_mul, one_mul, zero_mul]
  simp only [Finset.mul_sum]

theorem incidenceGame_perfect_of_zero_rejected
    (p : CorrelationTable R C (Fin 3 → ZMod 2) (ZMod 2)) (hp : IsProbabilityTable p)
    (hz : ∀ r i a b, ¬ S.Accepts r i a b → p r (S.column r i) a b = 0) :
    S.incidenceGame.success p = 1 := by
  have hr (r : R) (i : Fin 3) :
      (∑ a, ∑ b, if S.Accepts r i a b then p r (S.column r i) a b else 0) = 1 := by
    rw [← hp.normalized r (S.column r i)]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : S.Accepts r i a b
    · simp only [h, ite_true]
    · simp only [h, ite_false, hz r i a b h]
  rw [S.incidenceGame_success]
  simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hR : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  norm_num

end ThomGame.SparseSystem
