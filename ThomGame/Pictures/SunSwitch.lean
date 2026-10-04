module

public import ThomGame.Pictures.SunRimGraph
public import ThomGame.Pictures.PairingSurgery

/-!
# Switching an actual internal spoke of a sun graph

The two relation vertices are retained. Their second rim ports exchange
attachments, and both cyclic orders reverse. All other hub rotations and
all unaffected edge ends keep their identities. This file constructs the
graph; preservation of face returns requires the equal-orientation case.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v}

theorem sun_hub_eq_iff {h k : G.Hub} {i j : Fin 3} :
    (Port.hub h i : G.Dart) = .hub k j ↔ h = k ∧ i = j := by
  constructor
  · intro he
    cases he
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sun_rotation_hub (h : G.Hub) (i : Fin 3) :
    G.rotation (.hub h i) = .hub h
      ((if G.hubFlip h then (finRotate 3).symm else finRotate 3) i) := rfl

theorem sun_rotation_spoke_ne_spoke (h k : G.Hub) :
    G.rotation (.hub h (0 : Fin 3)) ≠ .hub k (0 : Fin 3) := by
  cases hf : G.hubFlip h
  · change Port.hub h (G.hubRotation h (0 : Fin 3)) ≠ .hub k (0 : Fin 3)
    rw [hubRotation, hf]
    change (Port.hub h (1 : Fin 3) : G.Dart) ≠ .hub k (0 : Fin 3)
    intro he
    cases he
  · change Port.hub h (G.hubRotation h (0 : Fin 3)) ≠ .hub k (0 : Fin 3)
    rw [hubRotation, hf]
    change (Port.hub h (2 : Fin 3) : G.Dart) ≠ .hub k (0 : Fin 3)
    intro he
    cases he

structure SunSpoke (G : PortGraph (sunPresentation n b) u v) where
  left : G.Hub
  right : G.Hub
  paired : G.pairing.twin (.hub left (0 : Fin 3)) = .hub right (0 : Fin 3)

namespace SunSpoke

variable (s : G.SunSpoke)

theorem labels : G.hubLabel s.left = G.hubLabel s.right :=
  (G.sun_spoke_hub_endpoints s.paired).1.symm

theorem distinct : s.left ≠ s.right := (G.sun_spoke_hub_endpoints s.paired).2.2

theorem paired_right : G.pairing.twin (.hub s.right (0 : Fin 3)) = .hub s.left (0 : Fin 3) := by
  rw [← s.paired, G.pairing.involutive]

noncomputable def portSwap : Perm G.Dart := swap (.hub s.left (2 : Fin 3)) (.hub s.right (2 : Fin 3))

theorem portSwap_involutive : Function.Involutive s.portSwap := swap_apply_self _ _

theorem portSwap_label (x : G.Dart) : Port.label G.jointLabel (s.portSwap x) = Port.label G.jointLabel x := by
  apply Pairing.label_swap
  change Sum.inr (finRotate n (G.hubLabel s.left)) = Sum.inr (finRotate n (G.hubLabel s.right))
  rw [s.labels]

@[reducible] noncomputable def switch : PortGraph (sunPresentation n b) u v where
  Hub := G.Hub
  Joint := G.Joint
  hubFintype := G.hubFintype
  jointFintype := G.jointFintype
  hubLabel := G.hubLabel
  hubFlip h := if h = s.left ∨ h = s.right then !G.hubFlip h else G.hubFlip h
  jointLabel := G.jointLabel
  pairing := G.pairing.transport s.portSwap (Port.label G.jointLabel) s.portSwap_label

theorem switch_hub_card : Fintype.card s.switch.Hub = Fintype.card G.Hub := rfl
theorem switch_sign : s.switch.sign = G.sign := rfl
theorem switch_character (j : Fin n) : s.switch.character j = G.character j := rfl

theorem switch_flip_left : s.switch.hubFlip s.left = !G.hubFlip s.left := by simp
theorem switch_flip_right : s.switch.hubFlip s.right = !G.hubFlip s.right := by simp
theorem switch_flip_away {h : G.Hub} (hl : h ≠ s.left) (hr : h ≠ s.right) :
    s.switch.hubFlip h = G.hubFlip h := by simp [hl, hr]

theorem switch_twin (x : G.Dart) :
    s.switch.pairing.twin x = s.portSwap (G.pairing.twin (s.portSwap x)) := rfl

theorem switch_twin_portSwap (x : G.Dart) :
    s.switch.pairing.twin (s.portSwap x) = s.portSwap (G.pairing.twin x) := by
  rw [s.switch_twin, s.portSwap_involutive]

theorem portSwap_spoke_left : s.portSwap (.hub s.left (0 : Fin 3)) = .hub s.left (0 : Fin 3) := by
  apply swap_apply_of_ne_of_ne <;> simp [sun_hub_eq_iff]

theorem portSwap_spoke_right : s.portSwap (.hub s.right (0 : Fin 3)) = .hub s.right (0 : Fin 3) := by
  apply swap_apply_of_ne_of_ne <;> simp [sun_hub_eq_iff]

theorem switch_paired : s.switch.pairing.twin (.hub s.left (0 : Fin 3)) = .hub s.right (0 : Fin 3) := by
  rw [s.switch_twin, s.portSwap_spoke_left, s.paired, s.portSwap_spoke_right]

theorem switch_paired_right : s.switch.pairing.twin (.hub s.right (0 : Fin 3)) = .hub s.left (0 : Fin 3) := by
  rw [s.switch_twin, s.portSwap_spoke_right, s.paired_right, s.portSwap_spoke_left]

def Kept (x : G.Dart) : Prop := x ≠ .hub s.left (0 : Fin 3) ∧ x ≠ .hub s.right (0 : Fin 3)

theorem portSwap_kept_iff (x : G.Dart) : s.Kept (s.portSwap x) ↔ s.Kept x := by
  have hl : s.portSwap x = .hub s.left (0 : Fin 3) ↔ x = .hub s.left (0 : Fin 3) := by
    simpa only [s.portSwap_spoke_left] using s.portSwap.injective.eq_iff
      (a := x) (b := .hub s.left (0 : Fin 3))
  have hr : s.portSwap x = .hub s.right (0 : Fin 3) ↔ x = .hub s.right (0 : Fin 3) := by
    simpa only [s.portSwap_spoke_right] using s.portSwap.injective.eq_iff
      (a := x) (b := .hub s.right (0 : Fin 3))
  exact and_congr (not_congr hl) (not_congr hr)

noncomputable def keptSwap : Perm (Subtype s.Kept) :=
  s.portSwap.subtypeEquiv (fun x => (s.portSwap_kept_iff x).symm)

theorem twin_kept {x : G.Dart} (hx : s.Kept x) : s.Kept (G.pairing.twin x) := by
  constructor
  · intro he
    have h := congrArg G.pairing.twin he
    rw [G.pairing.involutive, s.paired] at h
    exact hx.2 h
  · intro he
    have h := congrArg G.pairing.twin he
    rw [G.pairing.involutive, s.paired_right] at h
    exact hx.1 h

theorem portSwap_of_vertex_away {x : G.Dart}
    (hl : x.vertex ≠ .inr (.inl s.left)) (hr : x.vertex ≠ .inr (.inl s.right)) :
    s.portSwap x = x := by
  apply swap_apply_of_ne_of_ne
  · intro hx; exact hl (congrArg Port.vertex hx)
  · intro hx; exact hr (congrArg Port.vertex hx)

theorem switch_rotation_away {x : G.Dart}
    (hl : x.vertex ≠ .inr (.inl s.left)) (hr : x.vertex ≠ .inr (.inl s.right)) :
    s.switch.rotation x = G.rotation x := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | joint j side => rfl
  | hub h i =>
    have hh : h ≠ s.left ∧ h ≠ s.right := by simpa only [Port.vertex, ne_eq, Sum.inr.injEq,
      Sum.inl.injEq] using (And.intro hl hr)
    change Port.hub h (s.switch.hubRotation h i) = Port.hub h (G.hubRotation h i)
    simp [hubRotation, hh.1, hh.2]

end SunSpoke
end ThomGame.Pictures.PortGraph
