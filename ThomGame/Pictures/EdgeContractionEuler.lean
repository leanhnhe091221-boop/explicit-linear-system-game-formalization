module

public import ThomGame.Pictures.LoopCutEuler

/-!
# Merging the ends of a non-loop edge

Swapping the two vertex targets and fixing the two paired edge ports
preserves the face permutation. If the old vertices were distinct, the
vertex-orbit count decreases by one, the edge-orbit count increases by
one, and connectivity and Euler saturation are preserved. The two fixed
ports remain in the finite set; deletion and diagram assembly are separate
steps.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity

variable {D : Type*} [DecidableEq D] (r t : Perm D)

theorem paired_swap_commute (ht : Function.Involutive t) (a : D) :
    t * swap a (t a) = swap a (t a) * t := by
  rw [mul_swap_eq_swap_mul, ht a, swap_comm (t a) a]

theorem contractEdge_product (ht : Function.Involutive t) (a : D) :
    splice t a (t a) * splice r a (t a) = t * r := by
  rw [splice, splice, mul_assoc, ← mul_assoc t, paired_swap_commute t ht a]
  simp only [← mul_assoc, swap_mul_self, one_mul]

variable [Finite D]

theorem contractEdge_count (ht : Function.Involutive t) (a : D)
    (hr : ¬ r.SameCycle a (t a)) :
    count (splice r a (t a)) (splice t a (t a)) = count r t := by
  have hne : a ≠ t a := fun he => hr (he.sameCycle r)
  have hv := orbit_card_join r hr
  have he := orbit_card_split t hne
    (show t.SameCycle a (t a) from Perm.SameCycle.rfl.apply_right)
  unfold count
  rw [contractEdge_product r t ht a]
  omega

/-- The merged vertex itself still connects the now fixed edge ports. -/
theorem contractEdge_ends_connected (a : D) (hr : ¬ r.SameCycle a (t a)) :
    Connected (splice r a (t a)) (splice t a (t a)) a (t a) := by
  apply (connected_swap_iff _ _ _ _).mpr
  exact sameCycle_connected _ _ (joins r hr)

theorem contractEdge_connected (a : D) (hr : ¬ r.SameCycle a (t a)) (x y : D) :
    Connected (splice r a (t a)) (splice t a (t a)) x y ↔ Connected r t x y := by
  have hOld : Connected r t a (t a) := Connected.circuit a
  have hNew := contractEdge_ends_connected r t a hr
  have swap_step {p f : Perm D} (h : Connected p f a (t a)) (z : D) :
      Connected p f z (swap a (t a) z) := by
    by_cases hza : z = a
    · rw [hza, swap_apply_left]
      exact h
    by_cases hzb : z = t a
    · rw [hzb, swap_apply_right]
      exact h.symm
    rw [swap_apply_of_ne_of_ne hza hzb]
    exact Connected.refl _
  constructor
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      exact (Connected.edge z).trans (swap_step hOld (r z))
    · intro z
      exact (Connected.circuit z).trans (swap_step hOld (t z))
  · intro h
    apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      have hh := (Connected.edge (p := splice r a (t a))
        (f := splice t a (t a)) z).trans (swap_step hNew (splice r a (t a) z))
      simpa only [splice_apply, swap_apply_self, id_eq] using hh
    · intro z
      have hh := (Connected.circuit (p := splice r a (t a))
        (f := splice t a (t a)) z).trans (swap_step hNew (splice t a (t a) z))
      simpa only [splice_apply, swap_apply_self, id_eq] using hh

theorem contractEdge_component_card (a : D) (hr : ¬ r.SameCycle a (t a)) :
    Nat.card (Component (splice r a (t a)) (splice t a (t a))) =
      Nat.card (Component r t) :=
  Nat.card_congr (componentEquiv _ _ _ _ (contractEdge_connected r t a hr))

theorem contractEdge_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (a : D) (hr : ¬ r.SameCycle a (t a)) :
    count (splice r a (t a)) (splice t a (t a)) =
      2 * Nat.card (Component (splice r a (t a)) (splice t a (t a))) := by
  rw [contractEdge_count r t ht a hr, contractEdge_component_card r t a hr, hEuler]

end ThomGame.Pictures.RotationEuler
