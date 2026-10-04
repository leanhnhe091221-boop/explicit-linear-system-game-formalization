module

public import ThomGame.Construction.WheelGraphWitness
public import ThomGame.Construction.WheelSunDiagrams

/-!
# Actual minimal Sigma graphs and their stellar sun witnesses

The state keeps the actual graph, Euler equality, odd sign and minimal
hub count. Hub connectivity and minimal zero-sign stellar germs follow
from proved component extraction. This entry point accepts graphs
constructed by surgery without requiring a smoothing from a diagram.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

theorem J_sigma_eq_one_iff_closed_minimal_state :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧ SigmaMinimalState H := by
  constructor
  · intro hj
    obtain ⟨d, hs, hm⟩ := J_sigma_eq_one_iff_closed_minimal_odd_diagram.mp hj
    obtain ⟨H, circles, ⟨t⟩, hJ⟩ := Smoothing.exists_without_junctions d.graph
    exact ⟨H, hJ, t.closedMinimalOddState hm hs (fun _ => by change 0 < 3; omega)⟩
  · rintro ⟨H, _, h⟩
    obtain ⟨d, _, _, hs, hm⟩ := h.exists_minimal_diagram (fun _ => by change 0 < 3; omega)
    exact J_sigma_eq_one_iff_closed_minimal_odd_diagram.mpr ⟨d, hs, hm⟩

namespace SigmaMinimalState

variable {H : SigmaGraph [] []} (h : SigmaMinimalState H)
    (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))

@[reducible] noncomputable def germGraph (s : Bool) :
    SigmaGraph [] ((closedSigmaRimCircuit H i a).frontierWord (!s)) :=
  (closedSigmaRimCircuit H i a).germGraph h.dualEuler s

@[reducible] noncomputable def regionGraph (s : Bool) :
    SigmaGraph ((closedSigmaRimCircuit H i a).frontierWord s) [] :=
  (closedSigmaRimCircuit H i a).regionGraph h.dualEuler s

theorem exists_minimal_stellar_germ (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ g : SigmaDiagram [] ((closedSigmaRimCircuit H i a).frontierWord (!s)),
      (g.labels : Multiset (Fin 1417152)) =
        (∑ x : (h.germGraph i a s).Hub, ([(h.germGraph i a s).hubLabel x] : Multiset (Fin 1417152))) ∧
      g.size = Fintype.card (h.germGraph i a s).Hub ∧ g.sign = 0 ∧ g.Minimal ∧
      (h.germGraph i a s).sign = 0 := by
  obtain ⟨hc⟩ := numberedWheelCycle_stellar_of_ne_odd i hi
  obtain ⟨s, g, hl, hn, hz, hm, hgs⟩ :=
    h.exists_minimal_stellar_rim_germ (numberedWheelCycles i) a hc
  exact ⟨s, g, hl, hn, hz, hm, hgs⟩

theorem exists_minimal_stellar_sun (hi : i ≠ oddWheelCycle) :
    ∃ s, ∃ e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
        [] (closedSigmaRimSunFrontierWord H i a (!s)),
      (e.labels : Multiset (Fin (wheelCycles i).length)) =
        (∑ x : (h.germGraph i a s).Hub,
          ([(h.germGraph i a s).hubLabel x] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      e.size = Fintype.card (h.germGraph i a s).Hub ∧ e.sign = 0 ∧
      e.Minimal ∧ e.CharacterMinimal ∧ (h.germGraph i a s).sign = 0 := by
  obtain ⟨s, g, hl, hn, hz, hm, hgs⟩ := h.exists_minimal_stellar_germ i a hi
  have hu : ∀ z ∈ ([] : List (Fin 1889684)),
      z ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge := by simp
  have hv := closedSigmaRimFrontierWord_in_neighbourhood H i a (!s)
  have he := sigmaToCycleSun_minimal i hi g hu hv hz hm
  refine ⟨s, (sigmaToCycleSun i).diagram g, ?_, he.1.trans hn,
    (sigmaToCycleSun i).sign_diagram_zero g (fun _ _ _ => rfl), he.2.1, he.2.2, hgs⟩
  rw [← hl, Multiset.filterMap_coe]
  exact Multiset.coe_eq_coe.mpr ((sigmaToCycleSun i).labels_diagram_perm g)

end SigmaMinimalState
end ThomGame.Construction
