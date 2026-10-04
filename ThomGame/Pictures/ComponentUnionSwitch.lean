module

public import ThomGame.Pictures.RibbonConnectivity

/-!
# The union of the two selected components under an attachment exchange

Conjugating one of the two graph permutations by a transposition may
split or merge the selected components. Their union of raw points is
unchanged. No pairing, finiteness, orientation or Euler premise is used.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv
open scoped Classical

variable {D : Type*} (p q : Perm D) (a b : D)

def RootUnion (x : D) : Prop := Connected p q a x ∨ Connected p q b x

theorem rootUnion_connected {x y : D} (h : Connected p q x y) :
    RootUnion p q a b x ↔ RootUnion p q a b y :=
  or_congr ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩
    ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩

theorem rootUnion_edge (x : D) : RootUnion p q a b (p x) = RootUnion p q a b x :=
  propext (rootUnion_connected p q a b (Connected.edge x)).symm

theorem rootUnion_circuit (x : D) : RootUnion p q a b (q x) = RootUnion p q a b x :=
  propext (rootUnion_connected p q a b (Connected.circuit x)).symm

theorem rootUnion_swap (x : D) : RootUnion p q a b (swap a b x) = RootUnion p q a b x := by
  have ha : RootUnion p q a b a := Or.inl (Connected.refl a)
  have hb : RootUnion p q a b b := Or.inr (Connected.refl b)
  by_cases hxa : x = a
  · subst x
    rw [swap_apply_left]
    exact propext (iff_of_true hb ha)
  by_cases hxb : x = b
  · subst x
    rw [swap_apply_right]
    exact propext (iff_of_true ha hb)
  · rw [swap_apply_of_ne_of_ne hxa hxb]

theorem rootUnion_conjugate_subset (r : Perm D)
    (hr : ∀ x, r (swap a b x) = swap a b (p x)) {x : D}
    (hx : RootUnion r q a b x) : RootUnion p q a b x := by
  have hp (z : D) : RootUnion p q a b (r z) = RootUnion p q a b z := by
    have he : r z = swap a b (p (swap a b z)) := by
      simpa only [swap_apply_self] using hr (swap a b z)
    rw [he, rootUnion_swap, rootUnion_edge, rootUnion_swap]
  rcases hx with hx | hx
  · exact (hx.invariant (RootUnion p q a b) hp (rootUnion_circuit p q a b)).mp
      (Or.inl (Connected.refl a))
  · exact (hx.invariant (RootUnion p q a b) hp (rootUnion_circuit p q a b)).mp
      (Or.inr (Connected.refl b))

theorem rootUnion_conjugate_iff (r : Perm D)
    (hr : ∀ x, r (swap a b x) = swap a b (p x)) (x : D) :
    RootUnion r q a b x ↔ RootUnion p q a b x := by
  have hi (z : D) : p (swap a b z) = swap a b (r z) := by
    have he := congrArg (swap a b) (hr (swap a b z))
    simpa only [swap_apply_self] using he.symm
  exact ⟨rootUnion_conjugate_subset p q a b r hr,
    rootUnion_conjugate_subset r q a b p hi⟩

end ThomGame.Pictures.RibbonConnectivity
