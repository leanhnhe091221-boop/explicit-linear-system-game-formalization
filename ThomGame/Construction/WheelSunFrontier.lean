module

public import ThomGame.Construction.WheelSunEmbedding
public import ThomGame.Pictures.RowGraphQuadEmbedding

/-!
# The actual normalized sun graph on the original Sigma frontier

The inclusion retains the complete port equivalence, including every
numbered boundary occurrence. The target boundary is the original word,
not just a word of the same length or a diagram with matching labels.
All canonical target rims are facial label covers. The existence theorem
retains the source diagram, its smoothing and circle list, and the actual
finite inward-switch trace.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

variable (i : WheelCycleIndex)
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  (G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w)
  (v : List (Fin 1889684))

/-- A structural inclusion, with invariants proved for its actual target graph. -/
structure IncludedWheelSun where
  graph : SigmaGraph [] v
  ports : G.Dart ≃ graph.Dart
  label : ∀ a, Port.label graph.jointLabel (ports a) =
    (numberedWheelSunEmbedding i).edge (Port.label G.jointLabel a)
  twin : ∀ a, graph.pairing.twin (ports a) = ports (G.pairing.twin a)
  rotation : ∀ a, graph.rotation (ports a) = ports (G.rotation a)
  boundaryLength : w.length = v.length
  bottom : ∀ j : Fin w.length, ports (.bottom j) = .bottom (finCongr boundaryLength j)
  quadPath : G.BoundaryQuadPath → graph.BoundaryQuadPath
  quadPath_first : ∀ q, (quadPath q).firstDart = ports q.firstDart
  quadPath_middle : ∀ q, (quadPath q).middleDart = ports q.middleDart
  quadPath_last : ∀ q, (quadPath q).lastDart = ports q.lastDart
  hub_relations : (∑ h : graph.Hub, ([graph.hubLabel h] : Multiset (Fin 1417152))) =
    (∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin (wheelCycles i).length))).map
      (numberedWheelSunEmbedding i).vertex
  hub_card : Fintype.card graph.Hub = Fintype.card G.Hub
  sign : graph.sign = 0
  noJoints : IsEmpty graph.Joint
  euler : RibbonConnectivity.eulerDefect graph.pairing.perm graph.circuitStep = 0
  noncrossing : graph.BoundaryNoncrossing
  sees : graph.BoundarySeesComponents
  noRim : ∀ z ∈ v, z ∉ Set.range (numberedWheelCycles i).edge
  facial_covers : ∀ a : graph.RimDart (numberedWheelCycles i),
    (∃ side, (graph.rimSimpleCircuit (numberedWheelCycles i) (by simp) noRim a).BoundsFaceOrbit side) ∧
      (graph.rimSimpleCircuit (numberedWheelCycles i) (by simp) noRim a).IsLabelCover

noncomputable def includeWheelSunAtFrontier
    (hmap : w.map (numberedWheelSunEmbedding i).edge = v)
    (hi : i ≠ oddWheelCycle) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)
    (hG : G.SunFaceState (wheelCycles i).length_ge_three hw)
    (hc : G.SunRimsFacialCovers (wheelCycles i).length_ge_three hw) :
    IncludedWheelSun i G v := by
  subst v
  letI : IsEmpty G.Joint := hG.noJoints
  refine {
    graph := includeWheelSunGraph i G
    ports := includeWheelSunPorts i G
    label := includeWheelSunPorts_label i G
    twin := includeWheelSunPorts_twin i G
    rotation := includeWheelSunPorts_rotation i G
    boundaryLength := (List.length_map (f := (numberedWheelSunEmbedding i).edge) (as := w)).symm
    bottom := fun _ => rfl
    quadPath := fun q => q.embedRows (numberedWheelSunEmbedding i)
    quadPath_first := fun q => q.embedRows_firstDart (numberedWheelSunEmbedding i)
    quadPath_middle := fun q => q.embedRows_middleDart (numberedWheelSunEmbedding i)
    quadPath_last := fun q => q.embedRows_lastDart (numberedWheelSunEmbedding i)
    hub_relations := includeWheelSunGraph_hub_relations i G
    hub_card := includeWheelSunGraph_hub_card i G
    sign := includeWheelSunGraph_sign i G hi
    noJoints := includeWheelSunGraph_noJoints i G
    euler := (includeWheelSunGraph_euler i G).trans hG.minimal.euler
    noncrossing := includeWheelSunGraph_noncrossing i G hG.minimal.noncrossing
    sees := includeWheelSunGraph_sees i G hG.minimal.sees
    noRim := includeWheelSunGraph_no_rim i hw
    facial_covers := ?_ }
  exact includedWheelSunRims_facial_covers i G hw hc

theorem smoothedSigmaRimGerm_exists_included_sun {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
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
      Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, e, G, cs, tSun, K, q, hm, hc, hGJ, hq, hK, hf, hl, hn, _, hGerm⟩ :=
    smoothedSigmaRimGerm_exists_sun_facial_cover_graph t hmin hs i a hi
  let L := includeWheelSunAtFrontier i K ((closedSigmaRimCircuit H i a).frontierWord (!side))
    (closedSigmaRimSunFrontierWord_map H i a (!side)) hi
    (closedSigmaRimSunFrontierWord_spokes H i a (!side)) hK hf
  exact ⟨side, e, G, cs, tSun, K, q, L, hm, hc, hGJ, hq, hK,
    L.hub_relations.trans (congrArg (Multiset.map (numberedWheelSunEmbedding i).vertex) hl),
    L.hub_card.trans hn, hGerm⟩

end ThomGame.Construction
