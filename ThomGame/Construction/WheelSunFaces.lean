module

public import ThomGame.Construction.WheelSunTermination
public import ThomGame.Pictures.SunFaceTermination

/-!
# Actual numbered stellar wheel germs reach sun graphs with facial rims

The genuine smoothing and its complete circle list, and the finite
inward switch trace, are all retained. The actual endpoint has face
orbits at every rim and the exact retracted relation multiset. Covering
of the base cycle and structural replacement are separate obligations.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem smoothedSigmaRimGerm_exists_sun_face_graph {d : SigmaDiagram [] []}
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
      (∑ h : K.Hub, ([K.hubLabel h] : Multiset (Fin (wheelCycles i).length))) =
        (∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      Fintype.card K.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧ K.sign = 0 ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, e, G, cs, tSun, K, q, hm, hc, hGJ, hKJ, hq, hNo, hK, hb, hl, hn, hz, hGerm⟩ :=
    smoothedSigmaRimGerm_exists_terminal_sun_graph t hmin hs i a hi
  exact ⟨side, e, G, cs, tSun, K, q, hm, hc, hGJ, hq,
    PortGraph.SunFaceState.of_terminal (wheelCycles i).length_ge_three
      (closedSigmaRimSunFrontierWord_spokes H i a (!side)) hK hKJ hb hNo, hl, hn, hz, hGerm⟩

end ThomGame.Construction
