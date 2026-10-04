module

public import ThomGame.Quantum.POVM
public import ThomGame.Quantum.CommutingStrategy

/-! Commuting strategies with general positive operator-valued measurements.

These strategies use actual Hilbert spaces, arbitrary finite POVMs and the usual
Born expectation of commuting effects. Projective strategies embed without changing
the space, state, or correlation table.
-/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable (X Y A B H : Type*) [Fintype A] [Fintype B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A commuting-operator strategy allowing general POVMs. -/
structure CommutingPOVMStrategy where
  state : H
  norm_state : ‖state‖ = 1
  alice : X → POVM H A
  bob : Y → POVM H B
  commute : ∀ x y a b, Commute ((alice x).effect a) ((bob y).effect b)

namespace CommutingPOVMStrategy

variable {X Y A B H} (S : CommutingPOVMStrategy X Y A B H)

noncomputable def correlation : CorrelationTable X Y A B :=
  fun x y a b =>
    (inner ℂ S.state ((S.alice x).effect a ((S.bob y).effect b S.state))).re

theorem correlation_nonneg (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.correlation x y a b := by
  have h : 0 ≤ (S.alice x).effect a * (S.bob y).effect b :=
    (S.commute x y a b).mul_nonneg ((S.alice x).positive a) ((S.bob y).positive b)
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp h).re_inner_nonneg_right S.state

omit [CompleteSpace H] in
theorem bob_marginal (x : X) (y : Y) (b : B) :
    (∑ a, S.correlation x y a b) =
      (inner ℂ S.state ((S.bob y).effect b S.state)).re := by
  simp only [correlation]
  rw [← Complex.re_sum, ← inner_sum, (S.alice x).sum_apply]

omit [CompleteSpace H] in
theorem alice_marginal (x : X) (y : Y) (a : A) :
    (∑ b, S.correlation x y a b) =
      (inner ℂ S.state ((S.alice x).effect a S.state)).re := by
  simp only [correlation]
  rw [← Complex.re_sum, ← inner_sum, ← map_sum, (S.bob y).sum_apply]

theorem correlation_normalized (x : X) (y : Y) :
    ∑ a, ∑ b, S.correlation x y a b = 1 := by
  simp only [S.alice_marginal]
  rw [← Complex.re_sum, ← inner_sum, (S.alice x).sum_apply]
  change RCLike.re (inner ℂ S.state S.state) = 1
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), S.norm_state, one_pow]

theorem isProbabilityTable : IsProbabilityTable S.correlation :=
  ⟨S.correlation_nonneg, S.correlation_normalized⟩

theorem noSignalling : NoSignalling S.correlation where
  alice x y y' a := (S.alice_marginal x y a).trans (S.alice_marginal x y' a).symm
  bob x x' y b := (S.bob_marginal x y b).trans (S.bob_marginal x' y b).symm

theorem correlation_le_one (x : X) (y : Y) (a : A) (b : B) :
    S.correlation x y a b ≤ 1 := S.isProbabilityTable.le_one x y a b

end CommutingPOVMStrategy

namespace CommutingStrategy

variable {X Y A B H} (S : CommutingStrategy X Y A B H)

/-- View a projective commuting strategy as a general POVM strategy. -/
def toPOVM : CommutingPOVMStrategy X Y A B H where
  state := S.state
  norm_state := S.norm_state
  alice x := (S.alice x).toPOVM
  bob y := (S.bob y).toPOVM
  commute := S.commute

@[simp] theorem toPOVM_correlation : S.toPOVM.correlation = S.correlation := by
  funext x y a b
  exact (S.correlation_inner x y a b).symm

end CommutingStrategy

end ThomGame.Quantum
