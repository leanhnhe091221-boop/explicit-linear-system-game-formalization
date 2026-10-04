module

public import Mathlib.Data.List.TakeDrop

/-!
# Structurally recursive sorting for kernel computations

The explicit recursion bounds make the functions reducible by the Lean kernel.
The bounds used by `sort` suffice for the usual merge-sort computation. The
membership theorem below holds even for smaller bounds and is enough for
the relation-set preservation argument.
-/

@[expose] public section

namespace ThomGame.KernelSort

variable {α : Type*}

def mergeFuel (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeFuel le fuel xs (y :: ys)
    else y :: mergeFuel le fuel (x :: xs) ys

def sortFuel (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, x :: y :: xs =>
    let all := x :: y :: xs
    let left := sortFuel le fuel (all.take (all.length / 2))
    let right := sortFuel le fuel (all.drop (all.length / 2))
    mergeFuel le all.length left right

def sort (le : α → α → Bool) (xs : List α) : List α := sortFuel le xs.length xs

/-- One checked merge joins two previously checked sorting computations.
The explicit lengths let certificates reuse the results of smaller computations. -/
theorem sortFuel_step (le : α → α → Bool) (fuel m n : Nat)
    (xs ys sx sy result : List α)
    (hx : xs.length = m) (hy : ys.length = n)
    (hsize : 2 ≤ m + n) (hhalf : (m + n) / 2 = m)
    (hsx : sortFuel le fuel xs = sx) (hsy : sortFuel le fuel ys = sy)
    (hmerge : mergeFuel le (m + n) sx sy = result) :
    sortFuel le (fuel + 1) (xs ++ ys) = result := by
  have hsplit (ws : List α) (hw : 2 ≤ ws.length) :
      sortFuel le (fuel + 1) ws =
        mergeFuel le ws.length
          (sortFuel le fuel (ws.take (ws.length / 2)))
          (sortFuel le fuel (ws.drop (ws.length / 2))) := by
    cases ws with
    | nil => simp at hw
    | cons a ws =>
      cases ws with
      | nil => simp at hw
      | cons b ws => rfl
  rw [hsplit _ (by simpa [List.length_append, hx, hy] using hsize),
    List.length_append, hx, hy, hhalf]
  rw [← hx, List.take_left, List.drop_left, hsx, hsy, hx, hmerge]

theorem mem_mergeFuel (le : α → α → Bool) (a : α) (fuel : Nat) (xs ys : List α) :
    a ∈ mergeFuel le fuel xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction fuel generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split <;> simp [ih, or_assoc, or_left_comm]

theorem mem_sortFuel (le : α → α → Bool) (a : α) (fuel : Nat) (xs : List α) :
    a ∈ sortFuel le fuel xs ↔ a ∈ xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        simp only [sortFuel, mem_mergeFuel, ih]
        rw [← List.mem_append, List.take_append_drop]

theorem mem_sort (le : α → α → Bool) (a : α) (xs : List α) :
    a ∈ sort le xs ↔ a ∈ xs := mem_sortFuel le a xs.length xs

end ThomGame.KernelSort
