module

public import ThomGame.Pictures.RotationEulerGraph

/-!
# Cutting one paired loop in an Euler-saturating permutation map

If the two ends of an edge belong to the same vertex orbit, fixing both
edge ports raises the dual Euler count by two. Saturation forces them
into distinct cut dual components. This is a purely finite statement.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] (r t : Perm D) (ht : Function.Involutive t)

omit [Finite D] in
include ht in
theorem leftDual_count : count (t * r) t = count r t := by
  have he : t * (t * r) = r := by
    ext x
    exact ht (r x)
  unfold count
  rw [he]
  omega

omit [Finite D] in
include ht in
theorem leftDual_connected (x y : D) : Connected (t * r) t x y ↔ Connected r t x y := by
  constructor
  · intro h
    exact h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
      (fun x => (Connected.edge x).trans (Connected.circuit (r x))) Connected.circuit
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro x
      have he : t ((t * r) x) = r x := ht (r x)
      have hh : Connected (t * r) t x (t ((t * r) x)) :=
        (Connected.edge x).trans (Connected.circuit ((t * r) x))
      rwa [he] at hh
    · exact Connected.circuit

omit [Finite D] in
include ht in
theorem leftDual_component_card : Nat.card (Component (t * r) t) = Nat.card (Component r t) :=
  Nat.card_congr (componentEquiv (t * r) t r t (leftDual_connected r t ht))

variable [DecidableEq D]

omit [Finite D] in
include ht in
theorem cutLoop_product (a : D) : splice t a (t a) * (t * r) = splice r a (t a) := by
  ext x
  simp only [Perm.mul_apply, splice_apply]
  exact congrArg (swap a (t a)) (ht (r x))

include ht in
theorem cutLoop_count (a : D) (hne : a ≠ t a) (hr : r.SameCycle a (t a)) :
    count (t * r) (splice t a (t a)) = count r t + 2 := by
  have he := orbit_card_split t hne (show t.SameCycle a (t a) from Perm.SameCycle.rfl.apply_right)
  have hf := orbit_card_split r hne hr
  unfold count
  rw [cutLoop_product r t ht a, he, hf]
  omega

include ht in
theorem cutLoop_separates (hEuler : count r t = 2 * Nat.card (Component r t))
    (a : D) (hne : a ≠ t a) (hr : r.SameCycle a (t a)) :
    ¬ Connected (t * r) (splice t a (t a)) a (t a) := by
  intro hc
  have hfix : splice t a (t a) a = a := by simp [splice_apply]
  have hcard := component_card_same_of_fixed (t * r) (splice t a (t a)) hfix hc
  rw [splice_splice, leftDual_component_card r t ht] at hcard
  have hbound := count_le_twice_components (t * r) (splice t a (t a))
    (removed_pair_involutive t ht a)
  rw [cutLoop_count r t ht a hne hr, ← hcard, hEuler] at hbound
  omega

end ThomGame.Pictures.RotationEuler
