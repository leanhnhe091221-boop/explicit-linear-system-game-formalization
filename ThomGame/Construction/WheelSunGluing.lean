module

public import ThomGame.Construction.WheelSunFrontier
public import ThomGame.Construction.WheelRegionDiagrams
public import ThomGame.Construction.WheelMinimalRecovery
public import ThomGame.Pictures.ClosedGluingCovers
public import ThomGame.Pictures.ConnectedGermPartition

/-!
# Gluing the included normalized sun to the actual complementary region

The output is an actual closed graph with a full smoothing certificate
and explicit circle records. Every complete facial cover in either input
has a specified surviving circuit. For the certified replacement of a
reduced minimal odd Sigma diagram, the result has the original size and
sign. A genuine minimal diagram realizes its exact relation multiset.

The realization is used only for bookkeeping and minimality. This does
not assert that its graph is isomorphic to the glued graph, or that old
circuits cut into arcs by the frontier are preserved.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

namespace IncludedWheelSun

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i K v) (E : SigmaGraph v [])

noncomputable def glue : ClosedGluingReduction L.graph E := L.graph.reduceClosedGluing E

@[reducible] noncomputable def rimCircuit (a : L.graph.RimDart (numberedWheelCycles i)) :
    L.graph.SimpleCircuit := L.graph.rimSimpleCircuit (numberedWheelCycles i) (by simp) L.noRim a

@[reducible] noncomputable def gluedRimCircuit (a : L.graph.RimDart (numberedWheelCycles i)) :
    (L.glue E).graph.SimpleCircuit := (L.glue E).leftCircuit (L.rimCircuit a) (L.facial_covers a).2

theorem gluedRimCircuit_port (a : L.graph.RimDart (numberedWheelCycles i))
    (x : Fin (L.rimCircuit a).length × Bool) :
    (L.glue E).trace.portEmbedding ((L.gluedRimCircuit E a).port x) =
      PortGraph.compLeftEmbedding L.graph E ((L.rimCircuit a).port x) :=
  (L.glue E).leftCircuit_port (L.rimCircuit a) (L.facial_covers a).2 x

theorem gluedRimCircuit_facial_cover (a : L.graph.RimDart (numberedWheelCycles i)) :
    (∃ side, (L.gluedRimCircuit E a).BoundsFaceOrbit side) ∧
      (L.gluedRimCircuit E a).IsLabelCover := by
  obtain ⟨⟨side, hf⟩, hc⟩ := L.facial_covers a
  exact ⟨⟨side, (L.glue E).leftCircuit_boundsFaceOrbit (L.rimCircuit a) hc side hf⟩,
    (L.glue E).leftCircuit_isLabelCover (L.rimCircuit a) hc⟩

theorem glue_hub_relations :
    (∑ h : (L.glue E).graph.Hub, ([(L.glue E).graph.hubLabel h] : Multiset (Fin 1417152))) =
      (∑ h : K.Hub, ([K.hubLabel h] : Multiset (Fin (wheelCycles i).length))).map
        (numberedWheelSunEmbedding i).vertex +
      ∑ h : E.Hub, ([E.hubLabel h] : Multiset (Fin 1417152)) := by
  rw [(L.glue E).hub_relations, L.hub_relations]

theorem glue_sign : (L.glue E).graph.sign = E.sign := by
  rw [(L.glue E).sign, L.sign, zero_add]

theorem exists_diagram : ∃ g : SigmaDiagram [] v,
    (g.labels : Multiset (Fin 1417152)) =
      (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) ∧
    g.size = Fintype.card L.graph.Hub ∧ g.sign = 0 := by
  obtain ⟨g, hl, hn, hs⟩ := L.graph.exists_diagram_of_bottom_invariants_preserving
    (fun _ => by change 0 < 3; decide +kernel) L.euler L.noncrossing L.sees
  exact ⟨g, hl, hn, hs.trans L.sign⟩

end IncludedWheelSun

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (closedSigmaRimSunFrontierWord H i a (!side))}
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)))

include t hmin hs in
theorem includedSunGluing_hub_card
    (hn : Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub) :
    Fintype.card (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub = d.size := by
  rw [ClosedGluingReduction.hub_card, hn]
  exact ((closedSigmaRimCircuit H i a).germ_region_hub_card_of_connected
    (reduced_minimal_odd_sigma_reachable t hmin hs)
    (t.dualEuler) side).trans
      (t.hub_card.trans d.graph_hub_card)

include t hmin hs in
theorem includedSunGluing_sign (hz : (smoothedSigmaRimGermGraph t i a side).sign = 0) :
    (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.sign = 1 := by
  rw [L.glue_sign]
  have h := (closedSigmaRimCircuit H i a).germ_region_sign_of_connected
    (reduced_minimal_odd_sigma_reachable t hmin hs)
    (t.dualEuler) side
  change (smoothedSigmaRimGermGraph t i a side).sign +
    (smoothedSigmaRimRegionGraph t i a (!side)).sign = H.sign at h
  rw [hz, zero_add] at h
  exact h.trans (t.sign.trans (d.graph_sign.trans hs))

include t hmin hs in
theorem includedSunGluing_exists_minimal_diagram
    (hn : Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub)
    (hz : (smoothedSigmaRimGermGraph t i a side).sign = 0) :
    ∃ f : SigmaDiagram [] [],
      (f.labels : Multiset (Fin 1417152)) =
        (∑ h : (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub,
          ([(L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.hubLabel h] : Multiset (Fin 1417152))) ∧
      f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  obtain ⟨g, hgl, _, _⟩ := L.exists_diagram
  obtain ⟨e, hel, _, _⟩ := smoothedSigmaRimRegion_exists_diagram t i a (!side)
  let r := L.glue (smoothedSigmaRimRegionGraph t i a (!side))
  have hl : ((g.comp e).labels : Multiset (Fin 1417152)) =
      ∑ h : r.graph.Hub, ([r.graph.hubLabel h] : Multiset (Fin 1417152)) := by
    change ((g.labels ++ e.labels : List (Fin 1417152)) : Multiset (Fin 1417152)) = _
    rw [← Multiset.coe_add, hgl, hel, ← r.hub_relations]
  have hc : (g.comp e).size = d.size := (r.graph.diagram_size_of_hub_labels hl).trans
    (includedSunGluing_hub_card t hmin hs i a side L hn)
  have hsign : (g.comp e).sign = 1 := (r.graph.diagram_sign_of_hub_labels hl).trans
    (includedSunGluing_sign t hmin hs i a side L hz)
  refine ⟨g.comp e, hl, hc, hsign, ?_⟩
  intro f hf
  rw [hc]
  exact hmin f (hf.trans (hsign.trans hs.symm))

include t hmin hs in
theorem smoothedSigmaRim_exists_normalized_gluing (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ cs : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length),
    ∃ _tSun : Smoothing e.graph G cs,
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ q : PortGraph.SunSwitchTrace G K,
    ∃ L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)),
      e.Minimal ∧ e.CharacterMinimal ∧ IsEmpty G.Joint ∧
      q.Inward (wheelCycles i).length_ge_three (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      K.SunFaceState (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) =
        ((∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex).map (numberedWheelSunEmbedding i).vertex ∧
      Fintype.card (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub = d.size ∧
      (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.sign = 1 ∧
      ∃ f : SigmaDiagram [] [],
        (f.labels : Multiset (Fin 1417152)) =
          (∑ h : (L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub,
            ([(L.glue (smoothedSigmaRimRegionGraph t i a (!side))).graph.hubLabel h] : Multiset (Fin 1417152))) ∧
        f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  obtain ⟨side, e, G, cs, tSun, K, q, L, hm, hc, hGJ, hq, hK, hl, hn, hz⟩ :=
    smoothedSigmaRimGerm_exists_included_sun i t hmin hs a hi
  exact ⟨side, e, G, cs, tSun, K, q, L, hm, hc, hGJ, hq, hK, hl,
    includedSunGluing_hub_card t hmin hs i a side L hn,
    includedSunGluing_sign t hmin hs i a side L hz,
    includedSunGluing_exists_minimal_diagram t hmin hs i a side L hn hz⟩

end ThomGame.Construction
