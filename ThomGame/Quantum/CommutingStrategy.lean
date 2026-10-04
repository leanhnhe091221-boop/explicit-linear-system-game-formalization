module

public import ThomGame.Quantum.ProjectiveMeasurement
public import ThomGame.Quantum.Correlation

/-! Commuting-operator strategies and the Born probabilities of their answers. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable (X Y A B H : Type*) [Fintype A] [Fintype B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure CommutingStrategy where
  state : H
  norm_state : ‖state‖ = 1
  alice : X → ProjectiveMeasurement H A
  bob : Y → ProjectiveMeasurement H B
  commute : ∀ x y a b, Commute ((alice x).proj a) ((bob y).proj b)

namespace CommutingStrategy

variable {X Y A B H} (S : CommutingStrategy X Y A B H)

noncomputable def correlation : CorrelationTable X Y A B :=
  fun x y a b => ‖(S.alice x).proj a ((S.bob y).proj b S.state)‖ ^ 2

theorem correlation_nonneg (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.correlation x y a b := sq_nonneg _

theorem apply_commute (x : X) (y : Y) (a : A) (b : B) (ξ : H) :
    (S.alice x).proj a ((S.bob y).proj b ξ) =
      (S.bob y).proj b ((S.alice x).proj a ξ) :=
  DFunLike.congr_fun (S.commute x y a b).eq ξ

theorem correlation_inner (x : X) (y : Y) (a : A) (b : B) :
    S.correlation x y a b =
      (inner ℂ S.state ((S.alice x).proj a ((S.bob y).proj b S.state))).re := by
  rw [correlation, (S.alice x).norm_sq_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ((S.bob y).selfAdjoint b).adjoint_eq,
    ← S.apply_commute, (S.bob y).apply_twice]

theorem bob_marginal (x : X) (y : Y) (b : B) :
    (∑ a, S.correlation x y a b) = ‖(S.bob y).proj b S.state‖ ^ 2 :=
  (S.alice x).sum_norm_sq _

theorem alice_marginal (x : X) (y : Y) (a : A) :
    (∑ b, S.correlation x y a b) = ‖(S.alice x).proj a S.state‖ ^ 2 := by
  simp only [correlation, S.apply_commute]
  exact (S.bob y).sum_norm_sq _

theorem correlation_normalized (x : X) (y : Y) : ∑ a, ∑ b, S.correlation x y a b = 1 := by
  simp only [S.alice_marginal, (S.alice x).sum_norm_sq, S.norm_state, one_pow]

theorem isProbabilityTable : IsProbabilityTable S.correlation :=
  ⟨S.correlation_nonneg, S.correlation_normalized⟩

theorem noSignalling : NoSignalling S.correlation where
  alice x y y' a := (S.alice_marginal x y a).trans (S.alice_marginal x y' a).symm
  bob x x' y b := (S.bob_marginal x y b).trans (S.bob_marginal x' y b).symm

theorem correlation_le_one (x : X) (y : Y) (a : A) (b : B) : S.correlation x y a b ≤ 1 :=
  S.isProbabilityTable.le_one x y a b

end CommutingStrategy

end ThomGame.Quantum
