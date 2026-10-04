module

public import ThomGame.Construction.WheelSunFaces
public import ThomGame.Pictures.SunFacialCovers

/-!
# Facial rim covers for the actual numbered stellar wheel germs

The endpoint is the actual graph of a finite inward-switch trace from a
genuine smoothing, with all circle records explicit. It has both the
exact face-orbit property and the distinct-endpoint-label cover property,
while retaining the specified retracted relation multiset and germ size.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem smoothedSigmaRimGerm_exists_sun_facial_cover_graph {d : SigmaDiagram [] []}
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
      e.Minimal ∧ e.CharacterMinimal ∧ IsEmpty G.Joint ∧
      q.Inward (wheelCycles i).length_ge_three (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      K.SunFaceState (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      K.SunRimsFacialCovers (wheelCycles i).length_ge_three
        (closedSigmaRimSunFrontierWord_spokes H i a (!side)) ∧
      (∑ h : K.Hub, ([K.hubLabel h] : Multiset (Fin (wheelCycles i).length))) =
        (∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      Fintype.card K.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧ K.sign = 0 ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, e, G, cs, tSun, K, q, hm, hc, hGJ, hq, hK, hl, hn, hz, hGerm⟩ :=
    smoothedSigmaRimGerm_exists_sun_face_graph t hmin hs i a hi
  exact ⟨side, e, G, cs, tSun, K, q, hm, hc, hGJ, hq, hK,
    hK.facial_covers (wheelCycles i).length_ge_three
      (closedSigmaRimSunFrontierWord_spokes H i a (!side)), hl, hn, hz, hGerm⟩

end ThomGame.Construction
