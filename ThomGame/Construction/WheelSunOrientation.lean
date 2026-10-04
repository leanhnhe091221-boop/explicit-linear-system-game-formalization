module

public import ThomGame.Construction.WheelSunDiagrams
public import ThomGame.Pictures.SunCancellationBottom

/-!
# Equal spoke orientations for the actual stellar sun witnesses

The witnesses retain the original retracted labels and exact size. Every
genuine smoothing of each witness has equal hub orientations across its
internal spokes, by the actual smaller-diagram cancellation contradiction.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem smoothedSigmaRimGerm_exists_oriented_sun_diagram {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ h : (smoothedSigmaRimGermGraph t i a s).Hub,
          ([(smoothedSigmaRimGermGraph t i a s).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (smoothedSigmaRimGermGraph t i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧ e.CharacterMinimal ∧
      (∀ (G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
          [] (closedSigmaRimSunFrontierWord H i a (!s)))
        (cs : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)),
        Smoothing e.graph G cs → ∀ p : G.SunSpoke, G.hubFlip p.left = G.hubFlip p.right) := by
  obtain ⟨s, e, hl, hn, hz, hm, hc⟩ :=
    smoothedSigmaRimGerm_exists_minimal_sun_diagram t hmin hs i a hi
  exact ⟨s, e, hl, hn, hz, hm, hc,
    fun _ _ u p => u.characterMinimal_sun_bottom_spoke_same_flip hc p⟩

theorem closedSigmaRimGerm_exists_oriented_sun_diagram (d : SigmaDiagram [] [])
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : d.graph.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord d.graph i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ h : (closedSigmaRimGermGraph d i a s).Hub,
          ([(closedSigmaRimGermGraph d i a s).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (closedSigmaRimGermGraph d i a s).Hub ∧
      e.sign = 0 ∧ e.Minimal ∧ e.CharacterMinimal ∧
      (∀ (G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
          [] (closedSigmaRimSunFrontierWord d.graph i a (!s)))
        (cs : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)),
        Smoothing e.graph G cs → ∀ p : G.SunSpoke, G.hubFlip p.left = G.hubFlip p.right) :=
  smoothedSigmaRimGerm_exists_oriented_sun_diagram (SigmaGraphWitness.ofDiagram d) hmin hs i a hi

end ThomGame.Construction
