module

public import ThomGame.Construction.WheelSunReverseFrontier
public import ThomGame.Construction.WheelSunGluing
public import ThomGame.Pictures.CappedClosedGluing
public import ThomGame.Pictures.BoundaryCircuitTransport

/-!
# Correctly oriented replacement by the normalized actual sun

Normalize on the reversed frontier, move that lower boundary to the top,
and place the actual complementary region on the bottom. The resulting
closed graph has Euler defect zero by explicit capped-map gluing. Its
full smoothing retains every normalized sun facial cover, the original
total hub count and odd sign, and has a minimal diagram with precisely
the same relation multiset. Old circuits crossing the interface still
require a separate preservation proof.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

namespace IncludedWheelSun

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i K v.reverse)

@[reducible] noncomputable def topGraph : SigmaGraph v [] :=
  L.graph.bottomTopGraph.cast (List.reverse_reverse v) rfl

@[reducible] noncomputable def topPorts : L.graph.Dart ≃ L.topGraph.Dart :=
  L.graph.bottomTopPorts.trans (L.graph.bottomTopGraph.castPorts (List.reverse_reverse v) rfl)

theorem topPorts_bottom (j : Fin v.reverse.length) :
    L.topPorts (.bottom j) = .top (finCongr (congrArg List.length (List.reverse_reverse v))
      (PortGraph.reverseWordIndex v.reverse j)) :=
  L.graph.bottomTopGraph.castPorts_top (List.reverse_reverse v) rfl _

theorem topPorts_label (a : L.graph.Dart) :
    Port.label L.topGraph.jointLabel (L.topPorts a) = Port.label L.graph.jointLabel a :=
  (L.graph.bottomTopGraph.castPorts_label _ _ _).trans (L.graph.bottomTopPorts_label a)

theorem topPorts_pairing (a : L.graph.Dart) :
    L.topGraph.pairing.perm (L.topPorts a) = L.topPorts (L.graph.pairing.perm a) := by
  change L.topGraph.pairing.perm
    (L.graph.bottomTopGraph.castPorts _ _ (L.graph.bottomTopPorts a)) = _
  rw [PortGraph.castPorts_pairing, L.graph.bottomTop_pairing]
  rfl

theorem topPorts_rotation (a : L.graph.Dart) :
    L.topGraph.rotation (L.topPorts a) = L.topPorts (L.graph.rotation a) := by
  change L.topGraph.rotation
    (L.graph.bottomTopGraph.castPorts _ _ (L.graph.bottomTopPorts a)) = _
  rw [PortGraph.castPorts_rotation, L.graph.bottomTop_rotation]
  rfl

theorem topGraph_hub_relations :
    (∑ h : L.topGraph.Hub, ([L.topGraph.hubLabel h] : Multiset (Fin 1417152))) =
      ∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152)) :=
  L.graph.bottomTopGraph.cast_hub_relations _ _

theorem topGraph_hub_card : Fintype.card L.topGraph.Hub = Fintype.card L.graph.Hub :=
  L.graph.bottomTopGraph.cast_hub_card _ _

theorem topGraph_sign : L.topGraph.sign = 0 :=
  (L.graph.bottomTopGraph.cast_sign _ _).trans (L.graph.bottomTop_sign.trans L.sign)

theorem topGraph_noJoints : IsEmpty L.topGraph.Joint :=
  L.graph.bottomTopGraph.cast_noJoints _ _ L.noJoints

theorem topGraph_euler : eulerDefect L.topGraph.pairing.perm L.topGraph.circuitStep = 0 :=
  (L.graph.bottomTopGraph.cast_eulerDefect _ _).trans (L.graph.bottomTop_eulerDefect.trans L.euler)

theorem topGraph_noncrossing : L.topGraph.BoundaryNoncrossing :=
  L.graph.bottomTopGraph.cast_boundaryNoncrossing _ _ (L.graph.bottomTop_boundaryNoncrossing L.noncrossing)

theorem topGraph_sees : L.topGraph.BoundarySeesComponents :=
  L.graph.bottomTopGraph.cast_boundarySeesComponents _ _ (L.graph.bottomTop_boundarySeesComponents L.sees)

theorem topGraph_capped_saturated :
    RotationEuler.count L.topGraph.cappedRotation L.topGraph.pairing.perm =
      2 * Nat.card (Component L.topGraph.cappedRotation L.topGraph.pairing.perm) :=
  L.topGraph.cappedRotation_saturated_of_boundary_invariants
    (fun _ => by change 0 < 3; decide +kernel) L.topGraph_euler L.topGraph_noncrossing L.topGraph_sees

@[reducible] noncomputable def topRimCircuit (a : L.graph.RimDart (numberedWheelCycles i)) :
    L.topGraph.SimpleCircuit :=
  (L.rimCircuit a).bottomTopCircuit.castBoundary (List.reverse_reverse v) rfl

theorem topRimCircuit_port (a : L.graph.RimDart (numberedWheelCycles i))
    (x : Fin (L.rimCircuit a).length × Bool) :
    (L.topRimCircuit a).port x = L.topPorts ((L.rimCircuit a).port x) :=
  ((L.rimCircuit a).bottomTopCircuit.castBoundary_port (List.reverse_reverse v) rfl x).trans
    (congrArg (L.graph.bottomTopGraph.castPorts (List.reverse_reverse v) rfl)
      ((L.rimCircuit a).bottomTopCircuit_port x))

theorem topRimCircuit_facial_cover (a : L.graph.RimDart (numberedWheelCycles i)) :
    (∃ side, (L.topRimCircuit a).BoundsFaceOrbit side) ∧ (L.topRimCircuit a).IsLabelCover := by
  obtain ⟨⟨side, hf⟩, hc⟩ := L.facial_covers a
  exact ⟨⟨side, (L.rimCircuit a).bottomTopCircuit.castBoundary_boundsFaceOrbit
    (List.reverse_reverse v) rfl side ((L.rimCircuit a).bottomTopCircuit_boundsFaceOrbit side hf)⟩,
    (L.rimCircuit a).bottomTopCircuit.castBoundary_isLabelCover
      (List.reverse_reverse v) rfl ((L.rimCircuit a).bottomTopCircuit_isLabelCover hc)⟩

variable (E : SigmaGraph v [])

noncomputable def orientedGlue : ClosedGluingReduction E.swapBoundary L.topGraph :=
  E.swapBoundary.reduceClosedGluing L.topGraph

@[reducible] noncomputable def orientedRimCircuit (a : L.graph.RimDart (numberedWheelCycles i)) :
    (L.orientedGlue E).graph.SimpleCircuit :=
  (L.orientedGlue E).rightCircuit (L.topRimCircuit a) (L.topRimCircuit_facial_cover a).2

theorem orientedRimCircuit_port (a : L.graph.RimDart (numberedWheelCycles i))
    (x : Fin (L.rimCircuit a).length × Bool) :
    (L.orientedGlue E).trace.portEmbedding ((L.orientedRimCircuit E a).port x) =
      PortGraph.compRightEmbedding E.swapBoundary L.topGraph (L.topPorts ((L.rimCircuit a).port x)) :=
  ((L.orientedGlue E).rightCircuit_port (L.topRimCircuit a) (L.topRimCircuit_facial_cover a).2 x).trans
    (congrArg (PortGraph.compRightEmbedding E.swapBoundary L.topGraph) (L.topRimCircuit_port a x))

theorem orientedRimCircuit_facial_cover (a : L.graph.RimDart (numberedWheelCycles i)) :
    (∃ side, (L.orientedRimCircuit E a).BoundsFaceOrbit side) ∧
      (L.orientedRimCircuit E a).IsLabelCover := by
  obtain ⟨⟨side, hf⟩, hc⟩ := L.topRimCircuit_facial_cover a
  exact ⟨⟨side, (L.orientedGlue E).rightCircuit_boundsFaceOrbit (L.topRimCircuit a) hc side hf⟩,
    (L.orientedGlue E).rightCircuit_isLabelCover (L.topRimCircuit a) hc⟩

theorem orientedGlue_hub_relations :
    (∑ h : (L.orientedGlue E).graph.Hub, ([(L.orientedGlue E).graph.hubLabel h] : Multiset (Fin 1417152))) =
      (∑ h : E.Hub, ([E.hubLabel h] : Multiset (Fin 1417152))) +
        (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) := by
  rw [ClosedGluingReduction.hub_relations, L.topGraph_hub_relations]
  rfl

theorem orientedGlue_hub_card : Fintype.card (L.orientedGlue E).graph.Hub =
    Fintype.card E.Hub + Fintype.card L.graph.Hub := by
  rw [ClosedGluingReduction.hub_card, L.topGraph_hub_card]
  rfl

theorem orientedGlue_sign : (L.orientedGlue E).graph.sign = E.sign := by
  rw [ClosedGluingReduction.sign, L.topGraph_sign, add_zero]
  exact E.swapBoundary_sign

theorem orientedGlue_euler
    (hE : RotationEuler.count E.swapBoundary.cappedRotation E.swapBoundary.pairing.perm =
      2 * Nat.card (Component E.swapBoundary.cappedRotation E.swapBoundary.pairing.perm)) :
    eulerDefect (L.orientedGlue E).graph.pairing.perm (L.orientedGlue E).graph.circuitStep = 0 :=
  (L.orientedGlue E).euler_of_capped
    (fun _ => by change 0 < 3; decide +kernel) (fun _ => by change 0 < 3; decide +kernel)
    hE L.topGraph_capped_saturated

end IncludedWheelSun

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)

include t in
omit [IsEmpty H.Joint] in
theorem includedSunOrientedGluing_euler :
    eulerDefect (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.pairing.perm
      (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.circuitStep = 0 :=
  L.orientedGlue_euler _ ((closedSigmaRimCircuit H i a).regionGraph_swapBoundary_capped_saturated
    (t.dualEuler) (!side))

include t hmin hs in
theorem includedSunOrientedGluing_hub_card
    (hn : Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub) :
    Fintype.card (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub = d.size := by
  rw [L.orientedGlue_hub_card, hn, Nat.add_comm]
  exact ((closedSigmaRimCircuit H i a).germ_region_hub_card_of_connected
    (reduced_minimal_odd_sigma_reachable t hmin hs)
    (t.dualEuler) side).trans
      (t.hub_card.trans d.graph_hub_card)

include t hmin hs in
theorem includedSunOrientedGluing_sign (hz : (smoothedSigmaRimGermGraph t i a side).sign = 0) :
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.sign = 1 := by
  rw [L.orientedGlue_sign]
  have h := (closedSigmaRimCircuit H i a).germ_region_sign_of_connected
    (reduced_minimal_odd_sigma_reachable t hmin hs)
    (t.dualEuler) side
  change (smoothedSigmaRimGermGraph t i a side).sign +
    (smoothedSigmaRimRegionGraph t i a (!side)).sign = H.sign at h
  rw [hz, zero_add] at h
  exact h.trans (t.sign.trans (d.graph_sign.trans hs))

include t hmin hs in
theorem includedSunOrientedGluing_exists_minimal_diagram
    (hn : Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub)
    (hz : (smoothedSigmaRimGermGraph t i a side).sign = 0) :
    ∃ f : SigmaDiagram [] [],
      (f.labels : Multiset (Fin 1417152)) =
        (∑ h : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub,
          ([(L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.hubLabel h] :
            Multiset (Fin 1417152))) ∧
      f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  let r := L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))
  obtain ⟨f, hl⟩ := r.graph.exists_closed_diagram_of_saturated
    (fun _ => by change 0 < 3; decide +kernel)
    (r.graph.rotationEuler_saturated_iff.mpr (includedSunOrientedGluing_euler t i a side L))
  have hc : f.size = d.size := (r.graph.diagram_size_of_hub_labels hl).trans
    (includedSunOrientedGluing_hub_card t hmin hs i a side L hn)
  have hsign : f.sign = 1 := (r.graph.diagram_sign_of_hub_labels hl).trans
    (includedSunOrientedGluing_sign t hmin hs i a side L hz)
  refine ⟨f, hl, hc, hsign, ?_⟩
  intro g hg
  rw [hc]
  exact hmin g (hg.trans (hsign.trans hs.symm))

include t hmin hs in
theorem smoothedSigmaRim_exists_oriented_normalized_gluing (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)).reverse,
    ∃ G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)).reverse,
    ∃ cs : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length),
    ∃ _tSun : Smoothing e.graph G cs,
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)).reverse,
    ∃ q : PortGraph.SunSwitchTrace G K,
    ∃ L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse,
      e.Minimal ∧ e.CharacterMinimal ∧ IsEmpty G.Joint ∧
      q.Inward (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_reverse_spokes H i a (!side)) ∧
      K.SunFaceState (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_reverse_spokes H i a (!side)) ∧
      (∑ h : L.graph.Hub, ([L.graph.hubLabel h] : Multiset (Fin 1417152))) =
        ((∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex).map (numberedWheelSunEmbedding i).vertex ∧
      Fintype.card (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub = d.size ∧
      (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.sign = 1 ∧
      eulerDefect (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.pairing.perm
        (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.circuitStep = 0 ∧
      ∃ f : SigmaDiagram [] [],
        (f.labels : Multiset (Fin 1417152)) =
          (∑ h : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.Hub,
            ([(L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.hubLabel h] :
              Multiset (Fin 1417152))) ∧
        f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  obtain ⟨side, e, G, cs, tSun, K, q, L, hm, hc, hGJ, hq, hK, hl, hn, hz⟩ :=
    smoothedSigmaRimGerm_exists_reversed_included_sun t hmin hs i a hi
  exact ⟨side, e, G, cs, tSun, K, q, L, hm, hc, hGJ, hq, hK, hl,
    includedSunOrientedGluing_hub_card t hmin hs i a side L hn,
    includedSunOrientedGluing_sign t hmin hs i a side L hz,
    includedSunOrientedGluing_euler t i a side L,
    includedSunOrientedGluing_exists_minimal_diagram t hmin hs i a side L hn hz⟩

end ThomGame.Construction
