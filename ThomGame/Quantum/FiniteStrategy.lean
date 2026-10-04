module

public import ThomGame.Quantum.CommutingStrategy
public import ThomGame.Quantum.TensorMeasurement

/-! Finite-dimensional bipartite quantum strategies on explicit tensor products. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped TensorProduct

abbrev LocalSpace (d : Nat) := EuclideanSpace ℂ (Fin d)
abbrev BipartiteSpace (d e : Nat) := LocalSpace d ⊗[ℂ] LocalSpace e

instance bipartiteSpaceComplete (d e : Nat) : CompleteSpace (BipartiteSpace d e) :=
  FiniteDimensional.complete ℂ _

variable (X Y A B : Type*) [Fintype A] [Fintype B]

structure FiniteStrategy where
  dimAlice : Nat
  dimBob : Nat
  dimAlice_pos : 0 < dimAlice
  dimBob_pos : 0 < dimBob
  state : BipartiteSpace dimAlice dimBob
  norm_state : ‖state‖ = 1
  alice : X → ProjectiveMeasurement (LocalSpace dimAlice) A
  bob : Y → ProjectiveMeasurement (LocalSpace dimBob) B

namespace FiniteStrategy

variable {X Y A B} (S : FiniteStrategy X Y A B)

noncomputable def toCommuting :
    CommutingStrategy X Y A B (BipartiteSpace S.dimAlice S.dimBob) where
  state := S.state
  norm_state := S.norm_state
  alice x := (S.alice x).tensorLeft
  bob y := (S.bob y).tensorRight
  commute x y a b := ProjectiveMeasurement.tensor_commute (S.alice x) (S.bob y) a b

noncomputable def correlation : CorrelationTable X Y A B := S.toCommuting.correlation

theorem correlation_born (x : X) (y : Y) (a : A) (b : B) :
    S.correlation x y a b =
      ‖TensorProduct.mapL ((S.alice x).proj a) ((S.bob y).proj b) S.state‖ ^ 2 := rfl

theorem isProbabilityTable : IsProbabilityTable S.correlation := S.toCommuting.isProbabilityTable

theorem noSignalling : NoSignalling S.correlation := S.toCommuting.noSignalling

/-- Deterministic local answers realized by one-dimensional tensor factors. -/
noncomputable def deterministic (α : X → A) (β : Y → B) : FiniteStrategy X Y A B where
  dimAlice := 1
  dimBob := 1
  dimAlice_pos := Nat.zero_lt_one
  dimBob_pos := Nat.zero_lt_one
  state := EuclideanSpace.single 0 1 ⊗ₜ[ℂ] EuclideanSpace.single 0 1
  norm_state := by simp
  alice x := ProjectiveMeasurement.deterministic (α x)
  bob y := ProjectiveMeasurement.deterministic (β y)

theorem deterministic_correlation [DecidableEq A] [DecidableEq B]
    (α : X → A) (β : Y → B) (x : X) (y : Y) (a : A) (b : B) :
    (deterministic α β).correlation x y a b = if a = α x ∧ b = β y then 1 else 0 := by
  change ‖((ProjectiveMeasurement.deterministic (H := LocalSpace 1) (α x)).proj a
      (EuclideanSpace.single 0 1)) ⊗ₜ[ℂ]
    ((ProjectiveMeasurement.deterministic (H := LocalSpace 1) (β y)).proj b
      (EuclideanSpace.single 0 1))‖ ^ 2 = _
  by_cases ha : a = α x <;> by_cases hb : b = β y <;>
    simp [ProjectiveMeasurement.deterministic_apply, ha, hb]

end FiniteStrategy

end ThomGame.Quantum
