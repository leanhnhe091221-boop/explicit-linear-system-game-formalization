module

public import ThomGame.Pictures.VertexSplitEuler

/-! # Joining vertices in different components preserves Euler saturation -/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] [DecidableEq D] (r t : Perm D) {a b : D}

theorem joinVertex_count (hab : ¬ Connected r t a b) :
    count (splice r a b) t = count r t - 2 := by
  have hr : ¬ r.SameCycle a b := fun h =>
    hab ((connected_swap_iff t r a b).mp (sameCycle_connected t r h))
  have hf : ¬ (t * r).SameCycle (t a) (t b) := fun h =>
    hab ((Connected.circuit a).trans
      ((sameCycle_mul_connected r t h).trans (Connected.circuit b).symm))
  have hv := orbit_card_join r hr
  have hc := orbit_card_join (t * r) hf
  unfold count
  rw [splitVertex_product]
  omega

theorem joinVertex_component_card (hab : ¬ Connected r t a b) :
    Nat.card (Component (splice r a b) t) + 1 = Nat.card (Component r t) := by
  have hr : ¬ r.SameCycle a b := fun h =>
    hab ((connected_swap_iff t r a b).mp (sameCycle_connected t r h))
  have hs := sameCycle_connected t (splice r a b) (joins r hr)
  have hc := component_card_join_of_seam t r hs
    (fun h => hab ((connected_swap_iff t r a b).mp h))
  rw [Nat.card_congr (componentEquiv t r r t (connected_swap_iff t r)),
    Nat.card_congr (componentEquiv t (splice r a b) (splice r a b) t
      (connected_swap_iff t (splice r a b)))] at hc
  exact hc

theorem joinVertex_saturated
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (hab : ¬ Connected r t a b) :
    count (splice r a b) t = 2 * Nat.card (Component (splice r a b) t) := by
  have he := joinVertex_count r t hab
  have hc := joinVertex_component_card r t hab
  omega

end ThomGame.Pictures.RotationEuler
