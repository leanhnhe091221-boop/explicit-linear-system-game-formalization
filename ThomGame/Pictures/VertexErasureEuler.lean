module

public import ThomGame.Pictures.VertexSplitEuler
public import ThomGame.Pictures.EdgeDeletionEuler

/-!
# Replacing selected vertex rotations by leaves preserves Euler saturation

The retained set is a union of full vertex orbits. A removed vertex is
split into singleton rotations one port at a time. Each operation splits
one existing orbit, so the vertex-splitting theorem applies. No embedding
of a separate diagram witness is used.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] [DecidableEq D] (r t : Perm D)
  (M : D → Prop) (hM : ∀ x, M (r x) ↔ M x)

include hM in
theorem retainRotation_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count (retainEdges r M hM) t = 2 * Nat.card (Component (retainEdges r M hM) t) := by
  let : Fintype D := Fintype.ofFinite D
  induction hn : r.support.card using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hall : ∀ x, ¬ M x → r x = x
    · have he : retainEdges r M hM = r := by
        ext x
        rw [retainEdges_apply]
        by_cases hx : M x
        · rw [ite_eq_left hx]
        · rw [ite_eq_right hx, hall x hx]
      simpa only [he] using hEuler
    · obtain ⟨a, ha, hmove⟩ : ∃ a, ¬ M a ∧ r a ≠ a := by
        push Not at hall
        exact hall
      let r₀ := splice r a (r a)
      have hlt : r₀.support.card < n := by
        rw [← hn]
        exact Perm.card_support_swap_mul hmove
      have hs := ih r₀.support.card hlt r₀ (deleteEdge_marking r M hM a ha)
        (splitVertex_saturated r t ht hEuler
          (show r.SameCycle a (r a) from Perm.SameCycle.rfl.apply_right)) rfl
      simpa only [r₀, retainEdges_deleteEdge r M hM a ha] using hs

end ThomGame.Pictures.RotationEuler
