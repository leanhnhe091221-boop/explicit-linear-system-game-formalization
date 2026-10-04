module

public import ThomGame.Finite.Words
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Count

/-!
# Substitution by pairs of involutions

Each original generator g is replaced by u_g v_g u_g v_g. A negative
letter reverses this block. The Boolean in the new generator labels u or v;
it is independent of the sign in the original group word.
-/

@[expose] public section

namespace ThomGame.InvolutionWords

variable {α : Type*}

abbrev Generator (α : Type*) := α × Bool

def pair (g : α) : List (Generator α) := [(g, false), (g, true)]

def block (g : α) : List (Generator α) := pair g ++ pair g

def letterBlock (a : α × Bool) : List (Generator α) :=
  if a.2 then block a.1 else (block a.1).reverse

def substitute (w : Word α) : List (Generator α) := w.flatMap letterBlock

theorem letterBlock_length (a : α × Bool) : (letterBlock a).length = 4 := by
  rcases a with ⟨g, positive⟩
  cases positive <;> simp [letterBlock, block, pair]

theorem substitute_length (w : Word α) : (substitute w).length = 4 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [substitute, List.flatMap_cons, List.length_append] at *
    rw [letterBlock_length, ih, List.length_cons]
    omega

theorem letterBlock_count_even [DecidableEq α] (a : α × Bool) (x : Generator α) :
    Even ((letterBlock a).count x) := by
  rcases a with ⟨g, positive⟩
  cases positive <;> simp only [letterBlock, Bool.false_eq_true, ite_false, ite_true,
    List.count_reverse, block, List.count_append]
  all_goals exact ⟨(pair g).count x, rfl⟩

theorem substitute_count_even [DecidableEq α] (w : Word α) (x : Generator α) :
    Even ((substitute w).count x) := by
  induction w with
  | nil => exact ⟨0, rfl⟩
  | cons a w ih =>
    simp only [substitute, List.flatMap_cons, List.count_append]
    exact (letterBlock_count_even a x).add ih

end ThomGame.InvolutionWords
