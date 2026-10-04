module

public import ThomGame.Pictures.SunSwitchBoundary

/-!
# Exact rim-walk formula for a sun switch

Rim continuation exchanges the two rim ports of each hub, independently
of its orientation. The actual switch conjugates the rim edge pairing
by the exchange of the two second ports. We retain this exact port
correspondence, rather than only counting rim components.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)

noncomputable instance : Fintype (G.SunRimDart hn) := by
  unfold SunRimDart sunRowGraph RimDart
  infer_instance

def sunRimPort (h : G.Hub) : Bool → G.SunRimDart hn
  | false => ⟨.hub h (1 : Fin 3), ⟨G.hubLabel h, rfl⟩⟩
  | true => ⟨.hub h (2 : Fin 3), ⟨finRotate n (G.hubLabel h), rfl⟩⟩

theorem sunRimPort_ne (h : G.Hub) (side : Bool) :
    G.sunRimPort hn h (!side) ≠ G.sunRimPort hn h side := by
  intro he
  have hv := congrArg Subtype.val he
  cases side <;> cases hv

def sunRimPairing : Pairing (fun a : G.SunRimDart hn => Port.label G.jointLabel a.val) :=
  (G.sunRowGraph hn).rimPairing (Hypergraph.sunCycle n hn)

variable (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

noncomputable def sunRimVertexPairing : Pairing (fun a : G.SunRimDart hn => a.val.vertex) :=
  (G.sunRowGraph hn).rimVertexPairing (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv)

noncomputable def sunRimWalk : Perm (G.SunRimDart hn) :=
  (G.sunRimPairing hn).perm.trans (G.sunRimVertexPairing hn hu hv).perm

theorem sunRimVertexPairing_port (h : G.Hub) (side : Bool) :
    (G.sunRimVertexPairing hn hu hv).twin (G.sunRimPort hn h side) =
      G.sunRimPort hn h (!side) := by
  symm
  apply (G.sunRowGraph hn).rimSwitch_unique (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv)
  · cases side <;> rfl
  · exact G.sunRimPort_ne hn h side

namespace SunSpoke

variable {G} (s : G.SunSpoke)

noncomputable def rimSwap (side : Bool) : Perm (G.SunRimDart hn) :=
  swap (G.sunRimPort hn s.left side) (G.sunRimPort hn s.right side)

theorem rimSwap_involutive (side : Bool) : Function.Involutive (s.rimSwap hn side) :=
  swap_apply_self _ _

theorem rimSwap_true_val (a : G.SunRimDart hn) :
    (s.rimSwap hn true a).val = s.portSwap a.val := by
  exact @Function.Injective.map_swap (G.SunRimDart hn) G.Dart
    (Classical.decEq _) (Classical.decEq _) Subtype.val Subtype.val_injective
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) a

theorem switch_rimPairing (a : G.SunRimDart hn) :
    (s.switch.sunRimPairing hn).twin (s.rimSwap hn true a) =
      s.rimSwap hn true ((G.sunRimPairing hn).twin a) := by
  apply Subtype.ext
  change s.switch.pairing.twin (s.rimSwap hn true a).val = _
  exact (congrArg s.switch.pairing.twin (s.rimSwap_true_val hn a)).trans
    ((s.switch_twin_portSwap a.val).trans (s.rimSwap_true_val hn ((G.sunRimPairing hn).twin a)).symm)

theorem switch_rimVertexPairing (a : G.SunRimDart hn) :
    (s.switch.sunRimVertexPairing hn hu hv).twin a = (G.sunRimVertexPairing hn hu hv).twin a := by
  symm
  apply (s.switch.sunRowGraph hn).rimSwitch_unique (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv)
  · exact (G.sunRowGraph hn).rimSwitch_vertex (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a
  · exact (G.sunRowGraph hn).rimSwitch_ne_self (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a

theorem rimVertexPairing_rimSwap (side : Bool) (a : G.SunRimDart hn) :
    (G.sunRimVertexPairing hn hu hv).twin (s.rimSwap hn side a) =
      s.rimSwap hn (!side) ((G.sunRimVertexPairing hn hu hv).twin a) := by
  have h := (G.sunRimVertexPairing hn hu hv).perm.injective.map_swap
    (G.sunRimPort hn s.left side) (G.sunRimPort hn s.right side) a
  change (G.sunRimVertexPairing hn hu hv).twin (s.rimSwap hn side a) =
    swap ((G.sunRimVertexPairing hn hu hv).twin (G.sunRimPort hn s.left side))
      ((G.sunRimVertexPairing hn hu hv).twin (G.sunRimPort hn s.right side))
      ((G.sunRimVertexPairing hn hu hv).twin a) at h
  rw [G.sunRimVertexPairing_port, G.sunRimVertexPairing_port] at h
  exact h

theorem switch_rimWalk (a : G.SunRimDart hn) :
    s.switch.sunRimWalk hn hu hv (s.rimSwap hn true a) =
      s.rimSwap hn false (G.sunRimWalk hn hu hv a) := by
  change (s.switch.sunRimVertexPairing hn hu hv).twin
    ((s.switch.sunRimPairing hn).twin (s.rimSwap hn true a)) = _
  rw [s.switch_rimPairing, s.switch_rimVertexPairing, s.rimVertexPairing_rimSwap]
  rfl

noncomputable def switchedRimWalk : Perm (G.SunRimDart hn) := s.switch.sunRimWalk hn hu hv

theorem switch_rimWalk_conjugate :
    s.rimSwap hn true * s.switchedRimWalk hn hu hv * s.rimSwap hn true =
      s.rimSwap hn true * s.rimSwap hn false * G.sunRimWalk hn hu hv := by
  ext a
  exact congrArg (s.rimSwap hn true) (s.switch_rimWalk hn hu hv a)

end SunSpoke
end ThomGame.Pictures.PortGraph
