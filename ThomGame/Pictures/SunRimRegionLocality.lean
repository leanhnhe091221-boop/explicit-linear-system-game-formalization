module

public import ThomGame.Pictures.SunRegionLocality
public import ThomGame.Pictures.SunRimMembership
public import ThomGame.Pictures.SunRimRegionMasks

/-!
# Both sides of every unaffected rim retain their original ports

Rim component membership identifies the actual circuit markings before
and after surgery. If the component misses the two selected hubs, its
cut retains the entire switched patch. Region locality therefore applies
to the actual cut pairings. The two side base ports agree, so the Boolean
side itself is preserved, without an unchosen relabelling of the sides.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (a : G.SunRimDart hn)

theorem switch_rim_basePort (side : Bool) :
    (s.switch.sunRimSimpleCircuit hn hu hv a).port (0, side) =
      (G.sunRimSimpleCircuit hn hu hv a).port (0, side) := by
  cases side
  · rfl
  · change (s.switch.sunRimSimpleCircuit hn hu hv a).incoming 0 =
      (G.sunRimSimpleCircuit hn hu hv a).incoming 0
    exact (s.switch.sunRimCircuit_incoming hn hu hv a 0).trans
      ((congrArg Subtype.val (s.switch_rimVertexPairing hn hu hv a)).trans
        (G.sunRimCircuit_incoming hn hu hv a 0).symm)

variable
  (ha : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.left true))
  (hb : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    a (G.sunRimPort hn s.right true))

include ha hb in
theorem rim_away_marked_portSwap_iff (x : G.Dart) :
    (G.sunRimSimpleCircuit hn hu hv a).Marked (s.portSwap x) ↔
      (G.sunRimSimpleCircuit hn hu hv a).Marked x := by
  have hm := s.rim_away_retains_patch hn hu hv a ha hb (2 : Fin 3)
  change (G.sunRimSimpleCircuit hn hu hv a).Marked (swap _ _ x) ↔ _
  exact Iff.of_eq (Pairing.label_swap (propext (iff_of_false hm.1 hm.2)) x)

include ha hb in
theorem switch_rim_cutPairing_away :
    (s.switch.sunRimSimpleCircuit hn hu hv a).cutPairing =
      RotationEuler.retainEdges s.switch.pairing.perm
        (fun x => ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked (s.portSwap x))
        (s.switch_mask_invariant (fun x => ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked x)
          (fun x => not_congr ((G.sunRimSimpleCircuit hn hu hv a).marked_twin_iff x))) := by
  ext x
  rw [(s.switch.sunRimSimpleCircuit hn hu hv a).cutPairing_eq_retainEdges]
  simp only [RotationEuler.retainEdges_apply, s.switch_rim_marked_away hn hu hv a ha hb,
    s.rim_away_marked_portSwap_iff hn hu hv a ha hb]

include ha hb in
theorem switch_rim_cut_connected_away (hf : G.hubFlip s.left = G.hubFlip s.right) (x y : G.Dart) :
    Connected s.switch.circuitStep (s.switch.sunRimSimpleCircuit hn hu hv a).cutPairing x y ↔
      Connected G.circuitStep (G.sunRimSimpleCircuit hn hu hv a).cutPairing x y := by
  rw [s.switch_rim_cutPairing_away hn hu hv a ha hb,
    (G.sunRimSimpleCircuit hn hu hv a).cutPairing_eq_retainEdges]
  exact s.cut_connected_locality (fun z => ¬ (G.sunRimSimpleCircuit hn hu hv a).Marked z)
    (fun z => not_congr ((G.sunRimSimpleCircuit hn hu hv a).marked_twin_iff z))
    (s.rim_away_retains_patch hn hu hv a ha hb) hf x y

include ha hb in
theorem switch_rim_onSide_away (hf : G.hubFlip s.left = G.hubFlip s.right) (side : Bool) (x : G.Dart) :
    (s.switch.sunRimSimpleCircuit hn hu hv a).OnSide side x ↔
      (G.sunRimSimpleCircuit hn hu hv a).OnSide side x := by
  change Connected s.switch.circuitStep (s.switch.sunRimSimpleCircuit hn hu hv a).cutPairing x
      ((s.switch.sunRimSimpleCircuit hn hu hv a).port (0, side)) ↔ _
  rw [s.switch_rim_basePort hn hu hv a side]
  exact s.switch_rim_cut_connected_away hn hu hv a ha hb hf x _

end ThomGame.Pictures.PortGraph.SunSpoke
