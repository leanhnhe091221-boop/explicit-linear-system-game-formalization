module

public import ThomGame.Quantum.POVM
public import ThomGame.Quantum.FiniteStrategy

/-! The manuscript's finite-dimensional strategies with arbitrary POVMs.

The spaces and states are the same concrete tensor products used by `FiniteStrategy`.
Only the local measurement type changes; no dilation is assumed in this definition.
-/

@[expose] public section
namespace ThomGame.Quantum

open scoped TensorProduct

variable (X Y A B : Type*) [Fintype A] [Fintype B]

/-- A unit vector on two arbitrary positive finite-dimensional local spaces,
with a POVM for each question. -/
structure FinitePOVMStrategy where
  dimAlice : Nat
  dimBob : Nat
  dimAlice_pos : 0 < dimAlice
  dimBob_pos : 0 < dimBob
  state : BipartiteSpace dimAlice dimBob
  norm_state : ‖state‖ = 1
  alice : X → POVM (LocalSpace dimAlice) A
  bob : Y → POVM (LocalSpace dimBob) B

namespace FinitePOVMStrategy

variable {X Y A B} (S : FinitePOVMStrategy X Y A B)

/-- The Born rule for general effects, without squaring the applied vector norm. -/
noncomputable def correlation : CorrelationTable X Y A B :=
  fun x y a b =>
    (inner ℂ S.state
      (TensorProduct.mapL ((S.alice x).effect a) ((S.bob y).effect b) S.state)).re

end FinitePOVMStrategy

namespace FiniteStrategy

variable {X Y A B} (S : FiniteStrategy X Y A B)

/-- View each projective measurement as a POVM, with the same spaces and state. -/
noncomputable def toPOVM : FinitePOVMStrategy X Y A B where
  dimAlice := S.dimAlice
  dimBob := S.dimBob
  dimAlice_pos := S.dimAlice_pos
  dimBob_pos := S.dimBob_pos
  state := S.state
  norm_state := S.norm_state
  alice x := (S.alice x).toPOVM
  bob y := (S.bob y).toPOVM

@[simp] theorem toPOVM_correlation : S.toPOVM.correlation = S.correlation := by
  funext x y a b
  exact (S.toCommuting.correlation_inner x y a b).symm

end FiniteStrategy

end ThomGame.Quantum
