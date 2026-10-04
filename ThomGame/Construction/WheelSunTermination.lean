module

public import ThomGame.Construction.WheelSunDiagrams
public import ThomGame.Pictures.SunReducedTermination

/-!
# Finite inward-spoke reduction for the actual stellar wheel germs

Start with the proved minimal sun witness for a stellar germ of an
actual numbered Sigma diagram, smooth all joints with an explicit circle
list, and perform a finite inward switch trace. The terminal graph keeps
the prescribed frontier word and exact retracted relation multiset, has
the original germ's size and zero sign, and has no inward internal spoke.
Facial covers and the embedding conclusion are not inferred here.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem smoothedSigmaRimGerm_exists_terminal_sun_graph {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ cs : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length),
    ∃ _tSun : Smoothing e.graph G cs,
    ∃ K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!side)),
    ∃ q : PortGraph.SunSwitchTrace G K,
      e.Minimal ∧ e.CharacterMinimal ∧ IsEmpty G.Joint ∧ IsEmpty K.Joint ∧
      q.Inward (wheelCycles i).length_ge_three (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      K.NoInteriorSunSpoke (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      K.SunMinimalState ∧ K.HubsReachBoundary ∧
      (∑ h : K.Hub, ([K.hubLabel h] : Multiset (Fin (wheelCycles i).length))) =
        (∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      Fintype.card K.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧ K.sign = 0 ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, e, hl, hsize, hzero, hm, hc, hGerm⟩ :=
    smoothedSigmaRimGerm_exists_minimal_sun_diagram_with_sign t hmin hs i a hi
  obtain ⟨G, cs, ⟨tSun⟩, hJ⟩ := Smoothing.exists_without_junctions e.graph
  let : IsEmpty G.Joint := hJ
  obtain ⟨K, q, hq, hNo, hKJ, hK, hboundary, hcard, hsign, _⟩ :=
    tSun.exists_terminal_sun_switches hc (wheelCycles i).length_ge_three
      (closedSigmaRimSunFrontierWord_spokes H i a (!side))
  exact ⟨side, e, G, cs, tSun, K, q, hm, hc, hJ, hKJ, hq, hNo, hK, hboundary,
    q.hub_relations.trans (tSun.hub_relations.trans (e.graph_hub_relations.trans hl)),
    hcard.trans hsize, hsign.trans hzero, hGerm⟩

end ThomGame.Construction
