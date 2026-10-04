module

public import ThomGame.Pictures.SunSideSpokes
public import Mathlib.Data.Fintype.Sum

/-!
# The two rim sides partition the spokes in their ambient component

The ambient component is defined by actual graph paths from the rim
base port. Its spoke edges split into the two cut-side edge subsets.
Other connected components are not silently assigned to either side.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem onSide_union_iff_connected (side : Bool) (x : G.Dart) :
    (C.OnSide side x ∨ C.OnSide (!side) x) ↔
      Connected G.circuitStep G.pairing.perm x C.cutBase := by
  have ht : C.OnSide true x ↔
      Connected G.circuitStep C.cutPairing x (G.pairing.twin C.cutBase) :=
    ⟨fun h => h.trans (C.cut_port_true_mate 0),
      fun h => h.trans (C.cut_port_true_mate 0).symm⟩
  have h : (C.OnSide false x ∨ C.OnSide true x) ↔
      Connected G.circuitStep G.pairing.perm x C.cutBase :=
    (or_congr Iff.rfl ht).trans (C.old_connected_base_iff x).symm
  cases side
  · exact h
  · exact or_comm.trans h

end SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)

def SunComponentSpoke (a : G.SunRimDart hn) (x : G.Dart) : Prop :=
  G.HasSunSpokeLabel x ∧ Connected G.circuitStep G.pairing.perm x a.val

theorem sunComponentSpoke_twin_iff (a : G.SunRimDart hn) (x : G.Dart) :
    G.SunComponentSpoke hn a (G.pairing.twin x) ↔ G.SunComponentSpoke hn a x := by
  have he : Connected G.circuitStep G.pairing.perm x (G.pairing.twin x) := Connected.circuit x
  exact and_congr (G.hasSunSpokeLabel_twin_iff x)
    ⟨fun h => he.trans h, fun h => he.symm.trans h⟩

abbrev SunComponentSpokeEdge (a : G.SunRimDart hn) :=
  {c : G.Edge // G.pairing.EdgePred (G.SunComponentSpoke hn a) c}

noncomputable def sunComponentSpokeCount (a : G.SunRimDart hn) : Nat :=
  Nat.card (G.SunComponentSpokeEdge hn a)

variable (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem sunComponentSpoke_iff_sides (a : G.SunRimDart hn) (side : Bool) (x : G.Dart) :
    G.SunComponentSpoke hn a x ↔ G.SunSideSpoke hn hu hv a side x ∨
      G.SunSideSpoke hn hu hv a (!side) x := by
  have h := (G.sunRimSimpleCircuit hn hu hv a).onSide_union_iff_connected side x
  constructor
  · rintro ⟨hl, hc⟩
    rcases h.mpr hc with hs | hs
    · exact Or.inl ⟨hl, hs⟩
    · exact Or.inr ⟨hl, hs⟩
  · rintro (⟨hl, hs⟩ | ⟨hl, hs⟩)
    · exact ⟨hl, h.mp (Or.inl hs)⟩
    · exact ⟨hl, h.mp (Or.inr hs)⟩

theorem sunComponentSpoke_edge_partition (a : G.SunRimDart hn) (side : Bool) (c : G.Edge) :
    G.pairing.EdgePred (G.SunComponentSpoke hn a) c ↔
      G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) c ∨
      G.pairing.EdgePred (G.SunSideSpoke hn hu hv a (!side)) c := by
  refine Quotient.inductionOn c fun x => ?_
  change G.pairing.EdgePred (G.SunComponentSpoke hn a) (G.pairing.edge x) ↔
    G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) (G.pairing.edge x) ∨
    G.pairing.EdgePred (G.SunSideSpoke hn hu hv a (!side)) (G.pairing.edge x)
  rw [G.pairing.edgePred_edge_iff _ (G.sunComponentSpoke_twin_iff hn a),
    G.sunSideSpoke_edge_iff, G.sunSideSpoke_edge_iff]
  exact G.sunComponentSpoke_iff_sides hn hu hv a side x

theorem sunSideSpoke_edges_disjoint
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (a : G.SunRimDart hn) (side : Bool) (c : G.Edge) :
    ¬ (G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) c ∧
      G.pairing.EdgePred (G.SunSideSpoke hn hu hv a (!side)) c) := by
  refine Quotient.inductionOn c fun x => ?_
  change ¬ (G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) (G.pairing.edge x) ∧
    G.pairing.EdgePred (G.SunSideSpoke hn hu hv a (!side)) (G.pairing.edge x))
  rw [G.sunSideSpoke_edge_iff, G.sunSideSpoke_edge_iff]
  rintro ⟨hl, hr⟩
  have he := (G.sunRimSimpleCircuit hn hu hv a).onSide_unique hEuler hl.2 hr.2
  cases side <;> cases he

theorem sunComponentSpokeCount_eq_sides
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (a : G.SunRimDart hn) (side : Bool) :
    G.sunComponentSpokeCount hn a =
      G.sunSideSpokeCount hn hu hv a side + G.sunSideSpokeCount hn hu hv a (!side) := by
  let L := G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side)
  let R := G.pairing.EdgePred (G.SunSideSpoke hn hu hv a (!side))
  have hd : Disjoint L R := by
    intro p hp hq c hc
    exact G.sunSideSpoke_edges_disjoint hn hu hv hEuler a side c ⟨hp c hc, hq c hc⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight
    (G.sunComponentSpoke_edge_partition hn hu hv a side))).trans
      ((Nat.card_congr (subtypeOrEquiv L R hd)).trans (Nat.card_sum))

namespace SunSpoke

variable {G} (s : G.SunSpoke)

theorem switch_dual_connected (x y : G.Dart) :
    Connected s.switch.circuitStep s.switch.pairing.perm x y ↔
      Connected G.circuitStep G.pairing.perm x y :=
  (RotationEuler.connected_swap_iff _ _ x y).trans
    ((s.switch_circuit_connected x y).trans (RotationEuler.connected_swap_iff _ _ x y))

theorem switch_componentSpoke (a : G.SunRimDart hn) (x : G.Dart) :
    G.SunComponentSpoke hn a x ↔ s.switch.SunComponentSpoke hn a (s.portSwap x) := by
  have hl : s.switch.HasSunSpokeLabel (s.portSwap x) ↔ G.HasSunSpokeLabel x := by
    change (∃ j, Port.label G.jointLabel (s.portSwap x) = Sum.inl j) ↔
      ∃ j, Port.label G.jointLabel x = Sum.inl j
    rw [s.portSwap_label]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hl.mpr hx, ?_⟩
    rw [s.portSwap_spoke_fixed hx]
    exact (s.switch_dual_connected x a.val).mpr hc
  · rintro ⟨hx, hc⟩
    have hx' := hl.mp hx
    rw [s.portSwap_spoke_fixed hx'] at hc
    exact ⟨hx', (s.switch_dual_connected x a.val).mp hc⟩

theorem switch_component_spoke_count (a : G.SunRimDart hn) :
    s.switch.sunComponentSpokeCount hn a = G.sunComponentSpokeCount hn a :=
  (G.pairing.edge_subset_card s.switch.pairing s.portSwap s.switch_twin_portSwap
    (G.SunComponentSpoke hn a) (s.switch.SunComponentSpoke hn a)
    (s.switch_componentSpoke hn a)).symm

end SunSpoke
end ThomGame.Pictures.PortGraph
