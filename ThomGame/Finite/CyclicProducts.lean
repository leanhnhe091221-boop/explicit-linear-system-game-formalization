module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Group

/-! Ordered telescoping products around a finite cycle in an arbitrary group. -/

@[expose] public section
namespace ThomGame

variable {G : Type*} [Group G]

theorem ofFn_telescope (k : Nat → G) (n : Nat) :
    (List.ofFn (fun i : Fin n => k i.val * (k (i.val + 1))⁻¹)).prod = k 0 * (k n)⁻¹ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have h := ih (fun i => k (i + 1))
    change (List.ofFn (fun i : Fin n => k (i.val + 1) * (k (i.val + 1 + 1))⁻¹)).prod =
      k 1 * (k (n + 1))⁻¹ at h
    change (k 0 * (k 1)⁻¹) *
      (List.ofFn (fun i : Fin n => k (i.val + 1) * (k (i.val + 1 + 1))⁻¹)).prod = _
    rw [h]
    group

theorem ofFn_cyclic_telescope {n : Nat} [NeZero n] (k : Fin n → G) :
    (List.ofFn (fun i => k i * (k (finRotate n i))⁻¹)).prod = 1 := by
  let klift (i : Nat) := k ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩
  have h := ofFn_telescope klift n
  have hi (i : Fin n) : klift i.val = k i := by
    dsimp [klift]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hs (i : Fin n) : klift (i.val + 1) = k (finRotate n i) := by
    rw [finRotate_apply]
    dsimp [klift]
    congr 1
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod]
  simp only [hi, hs] at h
  simpa [klift] using h

theorem ofFn_first_factor {n : Nat} [NeZero n] (q : G) (f : Fin n → G) :
    (List.ofFn (fun i => (if i = 0 then q else 1) * f i)).prod = q * (List.ofFn f).prod := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => simp [List.ofFn_succ, mul_assoc]

end ThomGame
