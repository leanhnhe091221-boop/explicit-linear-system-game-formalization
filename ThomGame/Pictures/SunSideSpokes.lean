module

public import ThomGame.Pictures.SunRimRegionLocality
public import ThomGame.Pictures.PairingEdgePredicates

/-!
# Actual spoke edges on either side of a rim

The count below is the cardinality of a subtype of the original edge
quotient. Both endpoints of a spoke give the same side predicate. For
an unaffected rim the actual switch yields a bijection of these edges,
preserving each Boolean side and its count. An outer side has not yet
been chosen; this is not the full normalization measure NE.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v)

def HasSunSpokeLabel (x : G.Dart) : Prop := ∃ j, Port.label G.jointLabel x = Sum.inl j

theorem hasSunSpokeLabel_twin_iff (x : G.Dart) :
    G.HasSunSpokeLabel (G.pairing.twin x) ↔ G.HasSunSpokeLabel x := by
  unfold HasSunSpokeLabel
  rw [G.pairing.label_twin]

variable (hn : 3 ≤ n) (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (a : G.SunRimDart hn)

theorem sunRimCircuit_spokeLabel_unmarked {x : G.Dart} (hx : G.HasSunSpokeLabel x) :
    ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked x := by
  intro hm
  obtain ⟨j, hj⟩ := hx
  obtain ⟨i, hi⟩ := G.sunRimCircuit_marked_rim hn hu hv a hm
  rw [hj] at hi
  cases hi

def SunSideSpoke (side : Bool) (x : G.Dart) : Prop :=
  G.HasSunSpokeLabel x ∧ (G.sunRimSimpleCircuit hn hu hv a).OnSide side x

theorem sunSideSpoke_twin_iff (side : Bool) (x : G.Dart) :
    G.SunSideSpoke hn hu hv a side (G.pairing.twin x) ↔ G.SunSideSpoke hn hu hv a side x := by
  constructor
  · rintro ⟨ht, hs⟩
    have hx := (G.hasSunSpokeLabel_twin_iff x).mp ht
    exact ⟨hx, ((G.sunRimSimpleCircuit hn hu hv a).onSide_twin_iff
      (G.sunRimCircuit_spokeLabel_unmarked hn hu hv a hx) side).mp hs⟩
  · rintro ⟨hx, hs⟩
    exact ⟨(G.hasSunSpokeLabel_twin_iff x).mpr hx,
      ((G.sunRimSimpleCircuit hn hu hv a).onSide_twin_iff
        (G.sunRimCircuit_spokeLabel_unmarked hn hu hv a hx) side).mpr hs⟩

abbrev SunSideSpokeEdge (side : Bool) :=
  {c : G.Edge // G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) c}

noncomputable def sunSideSpokeCount (side : Bool) : Nat := Nat.card (G.SunSideSpokeEdge hn hu hv a side)

theorem sunSideSpoke_edge_iff (side : Bool) (x : G.Dart) :
    G.pairing.EdgePred (G.SunSideSpoke hn hu hv a side) (G.pairing.edge x) ↔
      G.SunSideSpoke hn hu hv a side x :=
  G.pairing.edgePred_edge_iff _ (G.sunSideSpoke_twin_iff hn hu hv a side) x

namespace SunSpoke

variable {G} (s : G.SunSpoke)

theorem portSwap_spoke_fixed {x : G.Dart} (hx : G.HasSunSpokeLabel x) : s.portSwap x = x := by
  have hne (h : G.Hub) : x ≠ .hub h (2 : Fin 3) := by
    intro he
    obtain ⟨j, hj⟩ := hx
    rw [he] at hj
    cases hj
  exact swap_apply_of_ne_of_ne (hne s.left) (hne s.right)

theorem switch_spoke_twin_fixed {x : G.Dart} (hx : G.HasSunSpokeLabel x) :
    s.switch.pairing.twin x = G.pairing.twin x := by
  rw [s.switch_twin, s.portSwap_spoke_fixed hx,
    s.portSwap_spoke_fixed ((G.hasSunSpokeLabel_twin_iff x).mpr hx)]

variable
  (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.left true))
  (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.right true))

include ha hb in
theorem switch_sideSpoke_away (hf : G.hubFlip s.left = G.hubFlip s.right) (side : Bool) (x : G.Dart) :
    G.SunSideSpoke hn hu hv a side x ↔ s.switch.SunSideSpoke hn hu hv a side (s.portSwap x) := by
  have hl : s.switch.HasSunSpokeLabel (s.portSwap x) ↔ G.HasSunSpokeLabel x := by
    change (∃ j, Port.label G.jointLabel (s.portSwap x) = Sum.inl j) ↔
      ∃ j, Port.label G.jointLabel x = Sum.inl j
    rw [s.portSwap_label]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hl.mpr hx, ?_⟩
    rw [s.portSwap_spoke_fixed hx]
    exact (s.switch_rim_onSide_away hn hu hv a ha hb hf side x).mpr hs
  · rintro ⟨hx, hs⟩
    have hx' := hl.mp hx
    rw [s.portSwap_spoke_fixed hx'] at hs
    exact ⟨hx', (s.switch_rim_onSide_away hn hu hv a ha hb hf side x).mp hs⟩

noncomputable def sideSpokeEdgeEquiv (hf : G.hubFlip s.left = G.hubFlip s.right) (side : Bool) :
    G.SunSideSpokeEdge hn hu hv a side ≃ s.switch.SunSideSpokeEdge hn hu hv a side :=
  G.pairing.edgeSubsetEquiv s.switch.pairing s.portSwap s.switch_twin_portSwap
    (G.SunSideSpoke hn hu hv a side) (s.switch.SunSideSpoke hn hu hv a side)
    (s.switch_sideSpoke_away hn hu hv a ha hb hf side)

include ha hb in
theorem switch_rim_spoke_count_away (hf : G.hubFlip s.left = G.hubFlip s.right) (side : Bool) :
    s.switch.sunSideSpokeCount hn hu hv a side = G.sunSideSpokeCount hn hu hv a side :=
  (Nat.card_congr (s.sideSpokeEdgeEquiv hn hu hv a ha hb hf side)).symm

end SunSpoke
end ThomGame.Pictures.PortGraph
