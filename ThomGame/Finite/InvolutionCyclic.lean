module

public import ThomGame.Finite.InvolutionWords
public import ThomGame.Finite.CyclicWords
public import Mathlib.Data.Option.Basic

/-!
# Cyclic reduction under involution substitution

The ends of successive four-letter blocks agree exactly when the original
signed letters cancel. This also checks the wraparound edge of a word.
-/

@[expose] public section
namespace ThomGame.InvolutionWords

variable {α : Type*}

/-- Cyclic reduction for an unsigned word in involutions. -/
def IsCyclicallyReduced {β : Type*} (w : List β) : Prop := CyclicChain (· ≠ ·) w

theorem letterBlock_ne_nil (a : α × Bool) : letterBlock a ≠ [] := by
  intro h
  have := letterBlock_length a
  simp [h] at this

theorem substitute_ne_nil {w : Word α} (h : w ≠ []) : substitute w ≠ [] := by
  intro hz
  have hlen := substitute_length w
  have hpos := List.length_pos_iff.mpr h
  simp only [hz, List.length_nil] at hlen
  omega

theorem letterBlock_head (a : α × Bool) :
    (letterBlock a).head? = some (a.1, !a.2) := by
  rcases a with ⟨g, positive⟩
  cases positive <;> rfl

theorem letterBlock_last (a : α × Bool) :
    (letterBlock a).getLast? = some a := by
  rcases a with ⟨g, positive⟩
  cases positive <;> rfl

theorem substitute_head (w : Word α) :
    (substitute w).head? = w.head?.map (fun a => (a.1, !a.2)) := by
  cases w with
  | nil => rfl
  | cons a w =>
    change (letterBlock a ++ substitute w).head? = some (a.1, !a.2)
    rw [List.head?_append_of_ne_nil _ (letterBlock_ne_nil a), letterBlock_head]

theorem substitute_last (w : Word α) :
    (substitute w).getLast? = w.getLast? := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => simpa [substitute] using letterBlock_last a
    | cons b w =>
      change (letterBlock a ++ substitute (b :: w)).getLast? = (a :: b :: w).getLast?
      rw [List.getLast?_append_of_ne_nil _ (substitute_ne_nil (List.cons_ne_nil _ _)), ih]
      rfl

theorem letterBlock_isChain (a : α × Bool) : (letterBlock a).IsChain (· ≠ ·) := by
  rcases a with ⟨g, positive⟩
  cases positive <;> simp [letterBlock, block, pair, List.isChain_cons_cons]

theorem block_boundary_ne (a b : α × Bool) (h : a.1 = b.1 → a.2 = b.2) :
    a ≠ (b.1, !b.2) := by
  intro heq
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  have hsign := h hfst
  simp only [hsign, Bool.eq_not_self] at hsnd

theorem substitute_isChain {w : Word α} (h : FreeGroup.IsReduced w) :
    (substitute w).IsChain (· ≠ ·) := by
  rw [substitute, List.flatMap_def]
  rw [List.isChain_flatten (by
    simp only [List.mem_map]
    rintro ⟨a, _, ha⟩
    exact letterBlock_ne_nil a ha)]
  constructor
  · intro l hl
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
    exact letterBlock_isChain a
  · rw [List.isChain_map]
    apply h.imp
    intro a b hab
    simp only [letterBlock_last, letterBlock_head, Option.mem_some_iff]
    rintro _ rfl _ rfl
    exact block_boundary_ne a b hab

/-- Substitution sends every cyclically reduced signed word to a cyclically
reduced unsigned word in the corresponding involutions. -/
theorem substitute_cyclicallyReduced {w : Word α} (h : FreeGroup.IsCyclicallyReduced w) :
    IsCyclicallyReduced (substitute w) := by
  refine ⟨substitute_isChain h.1, ?_⟩
  simp only [substitute_last, substitute_head, Option.mem_map]
  rintro a ha _ ⟨b, hb, rfl⟩
  exact block_boundary_ne a b (h.2 a ha b hb)

end ThomGame.InvolutionWords
