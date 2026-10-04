module

public import ThomGame.Pictures.SunRimComponents

/-! # Actual rim markings are exactly the rim component's ports -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem sunRimCircuit_marked_iff_connected (a x : G.SunRimDart hn) :
    (G.sunRimSimpleCircuit hn hu hv a).Marked x.val ↔
      Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a x := by
  let C := G.sunRimSimpleCircuit hn hu hv a
  have hd (i : Fin C.length) : Connected (G.sunRimPairing hn).perm
      (G.sunRimVertexPairing hn hu hv).perm a (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i) := by
    apply PairingCycles.sameCycle_connected
    exact OrbitEnumeration.dart_sameCycle (G.sunRimWalk hn hu hv) a i
  constructor
  · rintro ⟨⟨i, side⟩, hi⟩
    cases side
    · have he : OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i = x := Subtype.ext hi
      exact he ▸ hd i
    · have he : (G.sunRimPairing hn).twin
          (OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a ((finRotate C.length).symm i)) = x :=
        Subtype.ext hi
      exact he ▸ (hd ((finRotate C.length).symm i)).trans (Connected.edge _)
  · intro hx
    have hc : (G.sunRowGraph hn).rimComponent (Hypergraph.sunCycle n hn)
        (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a =
      (G.sunRowGraph hn).rimComponent (Hypergraph.sunCycle n hn)
        (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) x := (component_eq_iff _ _ _ _).mpr hx
    obtain ⟨i, hi | hi⟩ := (G.sunRowGraph hn).rimSimpleCircuit_component_darts (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a x hc
    · exact ⟨(i, false), hi.symm⟩
    · rw [hi]
      exact (C.marked_twin_iff _).mpr ⟨(i, false), rfl⟩

theorem sunRimCircuit_marked_iff_of_connected (a z : G.SunRimDart hn)
    (haz : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a z) (x : G.Dart) :
    (G.sunRimSimpleCircuit hn hu hv a).Marked x ↔ (G.sunRimSimpleCircuit hn hu hv z).Marked x := by
  constructor
  · intro hm
    let y : G.SunRimDart hn := ⟨x, G.sunRimCircuit_marked_rim hn hu hv a hm⟩
    exact (G.sunRimCircuit_marked_iff_connected hn hu hv z y).mpr
      (haz.symm.trans ((G.sunRimCircuit_marked_iff_connected hn hu hv a y).mp hm))
  · intro hm
    let y : G.SunRimDart hn := ⟨x, G.sunRimCircuit_marked_rim hn hu hv z hm⟩
    exact (G.sunRimCircuit_marked_iff_connected hn hu hv a y).mpr
      (haz.trans ((G.sunRimCircuit_marked_iff_connected hn hu hv z y).mp hm))

theorem sunRimCircuit_onHub_iff_connected (a : G.SunRimDart hn) (h : G.Hub) :
    (G.sunRimSimpleCircuit hn hu hv a).OnCircuitVertex (.inr (.inl h)) ↔
      Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
        a (G.sunRimPort hn h true) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨side, hs⟩ := G.sunRimCircuit_dart_at_hub hn hu hv a i h hi
    have hm : (G.sunRimSimpleCircuit hn hu hv a).Marked (G.sunRimPort hn h side).val :=
      ⟨(i, false), hs⟩
    have hc := (G.sunRimCircuit_marked_iff_connected hn hu hv a _).mp hm
    cases side
    · have hp := Connected.circuit (p := (G.sunRimPairing hn).perm)
        (f := (G.sunRimVertexPairing hn hu hv).perm) (G.sunRimPort hn h false)
      change Connected _ _ _ ((G.sunRimVertexPairing hn hu hv).twin _) at hp
      rw [G.sunRimVertexPairing_port] at hp
      exact hc.trans hp
    · exact hc
  · intro hc
    exact (G.sunRimSimpleCircuit hn hu hv a).marked_onCircuitVertex
      ((G.sunRimCircuit_marked_iff_connected hn hu hv a _).mpr hc)

namespace SunSpoke

variable {G} (s : G.SunSpoke) (a : G.SunRimDart hn)
  (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.left true))
  (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.right true))

include ha hb in
theorem switch_rim_marked_away (x : G.Dart) :
    (s.switch.sunRimSimpleCircuit hn hu hv a).Marked x ↔
      (G.sunRimSimpleCircuit hn hu hv a).Marked x := by
  by_cases hx : Port.label G.jointLabel x ∈ Set.range (Hypergraph.sunCycle n hn).edge
  · let z : G.SunRimDart hn := ⟨x, hx⟩
    exact (s.switch.sunRimCircuit_marked_iff_connected hn hu hv a z).trans
      ((s.switch_rim_connected_away hn hu hv ha hb z).trans
        (G.sunRimCircuit_marked_iff_connected hn hu hv a z).symm)
  · constructor
    · intro h
      exact (hx (s.switch.sunRimCircuit_marked_rim hn hu hv a h)).elim
    · intro h
      exact (hx (G.sunRimCircuit_marked_rim hn hu hv a h)).elim

include ha hb in
theorem rim_away_retains_patch (i : Fin 3) :
    ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked (.hub s.left i) ∧
      ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked (.hub s.right i) := by
  constructor
  · intro hm
    exact ha ((G.sunRimCircuit_onHub_iff_connected hn hu hv a s.left).mp
      ((G.sunRimSimpleCircuit hn hu hv a).marked_onCircuitVertex hm))
  · intro hm
    exact hb ((G.sunRimCircuit_onHub_iff_connected hn hu hv a s.right).mp
      ((G.sunRimSimpleCircuit hn hu hv a).marked_onCircuitVertex hm))

end SunSpoke
end ThomGame.Pictures.PortGraph
