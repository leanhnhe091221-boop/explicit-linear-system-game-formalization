module

public import ThomGame.Finite.Words
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.List.Rotate

/-!
# Semantic correctness of word normalization

Cyclic reduction and rotation preserve the equation `word = 1` in every
target group. They need not preserve the word's value as a free-group element.
-/

@[expose] public section

namespace ThomGame.Word

variable {α G : Type*} [Group G]

theorem eval_rotate_eq_one_iff (f : α → G) (r : Word α) (k : Nat) :
    eval f (r.rotate k) = 1 ↔ eval f r = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, eval_rotation_eq_one_iff, List.take_append_drop]

theorem eval_reduceCyclically_eq_one_iff [DecidableEq α] (f : α → G) (r : Word α) :
    eval f (FreeGroup.reduceCyclically r) = 1 ↔ eval f r = 1 := by
  let c := FreeGroup.reduceCyclically.conjugator r
  let v := FreeGroup.reduceCyclically r
  have hs := congrArg (eval f) (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically r)
  change eval f (c ++ v ++ inverse c) = eval f r at hs
  simp only [eval_append, eval_inverse] at hs
  rw [← hs]
  exact conj_eq_one_iff.symm

end ThomGame.Word
