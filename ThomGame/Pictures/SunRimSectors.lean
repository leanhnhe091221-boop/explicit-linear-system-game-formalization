module

public import ThomGame.Pictures.SunRimSwitch

/-!
# The side of a spoke at an oriented rim vertex

The actual hub rotation determines which cut side contains its spoke.
This supplies the local orientation information needed to distinguish
splitting one rim from reconnecting its two opposite orientations.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem sector_of_rotation_port {a : G.Dart} (i : Fin C.length) (side : Bool)
    (h : G.rotation a = C.port (i, side)) : C.Sector (!side) a := by
  have hf : (C.edgeTwist * G.rotation) a =
      C.port (CircuitPermutations.edge C.length (i, side)) := by
    rw [Perm.mul_apply, h, C.edgeTwist_port]
  have hs : C.Sector (!side) ((C.edgeTwist * G.rotation) a) := by
    rw [hf]
    exact (C.sector_marked _ _).mpr (CircuitPermutations.edge_snd C.length (i, side)).symm
  exact hs.trans (show (C.edgeTwist * G.rotation).SameCycle a ((C.edgeTwist * G.rotation) a) from
    ⟨1, by simp⟩).symm

end SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (a : G.SunRimDart hn)

theorem sunRimCircuit_incoming (i : Fin (G.sunRimSimpleCircuit hn hu hv a).length) :
    (G.sunRimSimpleCircuit hn hu hv a).incoming i =
      ((G.sunRimVertexPairing hn hu hv).twin
        (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i)).val := by
  have he := (congrArg (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a)
    ((finRotate (OrbitEnumeration.length (G.sunRimWalk hn hu hv) a)).apply_symm_apply i)).symm.trans
      (OrbitEnumeration.dart_next (G.sunRimWalk hn hu hv) a ((finRotate _).symm i))
  have hq := congrArg (G.sunRimVertexPairing hn hu hv).twin he
  change (G.sunRimVertexPairing hn hu hv).twin (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i) =
    (G.sunRimVertexPairing hn hu hv).twin ((G.sunRimVertexPairing hn hu hv).twin
      ((G.sunRimPairing hn).twin (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a ((finRotate _).symm i)))) at hq
  rw [(G.sunRimVertexPairing hn hu hv).involutive] at hq
  exact (congrArg Subtype.val hq).symm

theorem sunRimCircuit_marked_rim {x : G.Dart}
    (hx : (G.sunRimSimpleCircuit hn hu hv a).Marked x) :
    Port.label G.jointLabel x ∈ Set.range (Hypergraph.sunCycle n hn).edge := by
  obtain ⟨⟨i, side⟩, rfl⟩ := hx
  cases side
  · exact (G.sunRowGraph hn).rimSimpleCircuit_rim (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a i
  · change Port.label G.jointLabel (G.pairing.twin _) ∈ _
    rw [G.pairing.label_twin]
    exact (G.sunRowGraph hn).rimSimpleCircuit_rim (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a _

theorem sunRimCircuit_spoke_unmarked (h : G.Hub) :
    ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked (.hub h (0 : Fin 3)) := by
  intro hm
  obtain ⟨j, hj⟩ := G.sunRimCircuit_marked_rim hn hu hv a hm
  cases hj

theorem sunRimCircuit_incoming_at_hub (i : Fin (G.sunRimSimpleCircuit hn hu hv a).length)
    (h : G.Hub) (side : Bool)
    (hout : (G.sunRimSimpleCircuit hn hu hv a).dart i = (G.sunRimPort hn h side).val) :
    (G.sunRimSimpleCircuit hn hu hv a).incoming i = (G.sunRimPort hn h (!side)).val := by
  have hi : OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i = G.sunRimPort hn h side :=
    Subtype.ext hout
  rw [G.sunRimCircuit_incoming, hi, G.sunRimVertexPairing_port]

theorem sunRimCircuit_spoke_onSide (i : Fin (G.sunRimSimpleCircuit hn hu hv a).length)
    (h : G.Hub) (side : Bool)
    (hout : (G.sunRimSimpleCircuit hn hu hv a).dart i = (G.sunRimPort hn h side).val) :
    (G.sunRimSimpleCircuit hn hu hv a).OnSide (xor (G.hubFlip h) side) (.hub h (0 : Fin 3)) := by
  let C := G.sunRimSimpleCircuit hn hu hv a
  have hin := G.sunRimCircuit_incoming_at_hub hn hu hv a i h side hout
  have hm := G.sunRimCircuit_spoke_unmarked hn hu hv a h
  cases side <;> cases hf : G.hubFlip h
  · apply C.sector_onSide hm
    apply C.sector_of_rotation_port i false
    change G.rotation (.hub h (0 : Fin 3)) = C.dart i
    rw [hout, G.sun_rotation_hub, hf]
    rfl
  · apply C.sector_onSide hm
    apply C.sector_of_rotation_port i true
    change G.rotation (.hub h (0 : Fin 3)) = C.incoming i
    rw [hin, G.sun_rotation_hub, hf]
    rfl
  · apply C.sector_onSide hm
    apply C.sector_of_rotation_port i true
    change G.rotation (.hub h (0 : Fin 3)) = C.incoming i
    rw [hin, G.sun_rotation_hub, hf]
    rfl
  · apply C.sector_onSide hm
    apply C.sector_of_rotation_port i false
    change G.rotation (.hub h (0 : Fin 3)) = C.dart i
    rw [hout, G.sun_rotation_hub, hf]
    rfl

end ThomGame.Pictures.PortGraph
