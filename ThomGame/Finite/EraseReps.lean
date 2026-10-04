module

public import Mathlib.Data.List.Basic

/-! Removing adjacent repetitions preserves list membership. -/

@[expose] public section

namespace ThomGame

private theorem mem_eraseReps_loop {α : Type*} [BEq α] [LawfulBEq α]
    (a current : α) (xs acc : List α) :
    a ∈ List.eraseRepsBy.loop (· == ·) current xs acc ↔
      a = current ∨ a ∈ xs ∨ a ∈ acc := by
  induction xs generalizing current acc with
  | nil => simp [List.eraseRepsBy.loop, or_comm]
  | cons x xs ih =>
    cases h : (current == x) with
    | false => simp [List.eraseRepsBy.loop, h, ih, or_assoc, or_left_comm]
    | true =>
      have heq : current = x := by simpa using h
      subst current
      simp [List.eraseRepsBy.loop, ih, or_assoc]

theorem mem_eraseReps {α : Type*} [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    a ∈ xs.eraseReps ↔ a ∈ xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [List.eraseReps, List.eraseRepsBy, mem_eraseReps_loop]

end ThomGame
