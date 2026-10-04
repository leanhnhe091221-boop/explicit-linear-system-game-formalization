module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Signed group words

The Boolean sign belongs to a letter, independently of any coefficient label
inside its generator. `true` means a generator; `false` means its group inverse.
This convention agrees with `FreeGroup.mk`.
-/

@[expose] public section

namespace ThomGame

/-- A finite signed word; it is syntax, not yet a quotient-group element. -/
abbrev Word (α : Type*) := List (α × Bool)

namespace Word

variable {α G : Type*} [Group G]

def generator (a : α) : Word α := [(a, true)]

def inverse (w : Word α) : Word α := FreeGroup.invRev w

/-- The convention throughout the paper is `[u,v] = u v u⁻¹ v⁻¹`. -/
def commutator (u v : Word α) : Word α := u ++ v ++ inverse u ++ inverse v

/-- The relation word associated to the equation `u = v`. -/
def equation (u v : Word α) : Word α := u ++ inverse v

def eval (f : α → G) (w : Word α) : G := FreeGroup.lift f (FreeGroup.mk w)

@[simp] theorem eval_generator (f : α → G) (a : α) : eval f (generator a) = f a := by
  simp [eval, generator, FreeGroup.lift_mk]

@[simp] theorem eval_nil (f : α → G) : eval f [] = 1 := by
  simp [eval, FreeGroup.lift_mk]

@[simp] theorem eval_append (f : α → G) (u v : Word α) :
    eval f (u ++ v) = eval f u * eval f v := by
  simp only [eval, ← FreeGroup.mul_mk, map_mul]

@[simp] theorem eval_inverse (f : α → G) (w : Word α) :
    eval f (inverse w) = (eval f w)⁻¹ := by
  simp only [eval, inverse, ← FreeGroup.inv_mk, map_inv]

@[simp] theorem eval_commutator (f : α → G) (u v : Word α) :
    eval f (commutator u v) = eval f u * eval f v * (eval f u)⁻¹ * (eval f v)⁻¹ := by
  simp [commutator, mul_assoc]

theorem eval_equation_eq_one_iff (f : α → G) (u v : Word α) :
    eval f (equation u v) = 1 ↔ eval f u = eval f v := by
  simp only [equation, eval_append, eval_inverse]
  exact mul_inv_eq_one

/-- Cyclic rotation preserves the equation represented by a relator.
It need not preserve the element of the free group itself. -/
theorem eval_rotation_eq_one_iff (f : α → G) (u v : Word α) :
    eval f (u ++ v) = 1 ↔ eval f (v ++ u) = 1 := by
  simp only [eval_append]
  exact mul_eq_one_comm

theorem eval_reduce [DecidableEq α] (f : α → G) (w : Word α) :
    eval f (FreeGroup.reduce w) = eval f w := by
  unfold eval
  rw [FreeGroup.reduce.self]

end Word

end ThomGame
