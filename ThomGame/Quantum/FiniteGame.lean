module

public import ThomGame.Quantum.Correlation
public import Mathlib.Topology.Algebra.Ring.Real

/-! Finite nonlocal games and their continuous linear payoff on correlation tables. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

structure FiniteGame where
  weight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ weight x y
  weight_sum : ∑ x, ∑ y, weight x y = 1
  payoff : X → Y → A → B → ℝ
  payoff_nonneg : ∀ x y a b, 0 ≤ payoff x y a b
  payoff_le_one : ∀ x y a b, payoff x y a b ≤ 1

namespace FiniteGame

variable {X Y A B} (G : FiniteGame X Y A B)

noncomputable def answerScore (p : CorrelationTable X Y A B) (x : X) (y : Y) : ℝ :=
  ∑ a, ∑ b, G.payoff x y a b * p x y a b

noncomputable def success (p : CorrelationTable X Y A B) : ℝ :=
  ∑ x, ∑ y, G.weight x y * G.answerScore p x y

theorem answerScore_nonneg {p : CorrelationTable X Y A B} (hp : IsProbabilityTable p)
    (x : X) (y : Y) : 0 ≤ G.answerScore p x y :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (G.payoff_nonneg x y a b) (hp.nonneg x y a b)))

theorem answerScore_le_one {p : CorrelationTable X Y A B} (hp : IsProbabilityTable p)
    (x : X) (y : Y) : G.answerScore p x y ≤ 1 := by
  calc
    G.answerScore p x y ≤ ∑ a, ∑ b, p x y a b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_of_le_one_left (hp.nonneg x y a b) (G.payoff_le_one x y a b)
    _ = 1 := hp.normalized x y

theorem success_nonneg {p : CorrelationTable X Y A B} (hp : IsProbabilityTable p) :
    0 ≤ G.success p :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
    mul_nonneg (G.weight_nonneg x y) (G.answerScore_nonneg hp x y)))

theorem success_le_one {p : CorrelationTable X Y A B} (hp : IsProbabilityTable p) :
    G.success p ≤ 1 := by
  calc
    G.success p ≤ ∑ x, ∑ y, G.weight x y := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_of_le_one_right (G.weight_nonneg x y) (G.answerScore_le_one hp x y)
    _ = 1 := G.weight_sum

theorem continuous_success : Continuous G.success := by
  unfold success answerScore
  fun_prop

theorem success_add (p q : CorrelationTable X Y A B) :
    G.success (p + q) = G.success p + G.success q := by
  simp [success, answerScore, mul_add, Finset.sum_add_distrib]

theorem success_smul (t : ℝ) (p : CorrelationTable X Y A B) :
    G.success (t • p) = t * G.success p := by
  simp [success, answerScore, mul_left_comm, Finset.mul_sum]

end FiniteGame

end ThomGame.Quantum
