module

public import ThomGame.Construction.WheelSunFrontier
public import ThomGame.Pictures.DiagramBottomReversal

/-!
# Normalizing the actual stellar sun on the reversed frontier

Reversing the initial minimal sun witness preserves its complete relation
multiset, size and sign. Smoothing and the finite inward-switch algorithm
then act on that reversed word. The inclusion into Sigma retains every
boundary position and every facial rim cover in the resulting graph.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem closedSigmaRimSunFrontierWord_reverse_spokes (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) (s : Bool) :
    ∀ z ∈ (closedSigmaRimSunFrontierWord G i a s).reverse, ∃ j, z = Sum.inl j := by
  simpa only [List.mem_reverse] using closedSigmaRimSunFrontierWord_spokes G i a s

theorem smoothedSigmaRimGerm_exists_reversed_included_sun {d : SigmaDiagram [] []}
    {H : SigmaGraph [] []}  (t : SigmaGraphWitness d H)
    (hmin : d.Minimal) (hs : d.sign = 1)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (hi : i ≠ oddWheelCycle) :
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
      Fintype.card L.graph.Hub = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, f, hl, hn, _, hm, _, hz⟩ :=
    smoothedSigmaRimGerm_exists_minimal_sun_diagram_with_sign t hmin hs i a hi
  let e := f.reverseBottom
  have hminE : e.Minimal := hm.reverseBottom
  have hcharE : e.CharacterMinimal := hminE.characterMinimal
  obtain ⟨G, cs, ⟨tSun⟩, hGJ⟩ := Smoothing.exists_without_junctions e.graph
  let : IsEmpty G.Joint := hGJ
  have hw := closedSigmaRimSunFrontierWord_reverse_spokes H i a (!side)
  obtain ⟨K, q, hq, hK, hf, hkl, hkn, _, _, _⟩ :=
    tSun.exists_sun_facial_cover_switches (wheelCycles i).length_ge_three hw hcharE
  have hmap : (closedSigmaRimSunFrontierWord H i a (!side)).reverse.map
      (numberedWheelSunEmbedding i).edge =
        ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse := by
    rw [List.map_reverse]
    exact congrArg List.reverse (closedSigmaRimSunFrontierWord_map H i a (!side))
  let L := includeWheelSunAtFrontier i K _ hmap hi hw hK hf
  have hel : (e.labels : Multiset (Fin (wheelCycles i).length)) = (f.labels : Multiset _) :=
    Multiset.coe_eq_coe.mpr f.labels_reverseBottom_perm
  exact ⟨side, e, G, cs, tSun, K, q, L, hminE, hcharE, hGJ, hq, hK,
    L.hub_relations.trans (congrArg (Multiset.map (numberedWheelSunEmbedding i).vertex)
      (hkl.trans (hel.trans hl))),
    L.hub_card.trans (hkn.trans (f.size_reverseBottom.trans hn)), hz⟩

end ThomGame.Construction
