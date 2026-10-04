module

public import ThomGame.Pictures.CircuitRegionDiagram
public import ThomGame.Pictures.CircuitGermDiagram
public import ThomGame.Pictures.MinimalSmoothedGerm

/-!
# Minimality of actual region and germ diagram witnesses

Replacing either factor of a closed composition preserves its sign when
the replacement has the same boundary and sign. Exact hub counts make
any smaller region or germ witness contradict minimality of the original
closed diagram. Circuits in components with no hubs give size-zero
witnesses. The argument needs no graph isomorphism between witnesses.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace Diagram

theorem minimal_closed_factors {w : List S} (d : Diagram P [] []) (hmin : d.Minimal)
    (g : Diagram P [] w) (e : Diagram P w [])
    (hsize : g.size + e.size = d.size) (hsign : g.sign + e.sign = d.sign) :
    g.Minimal ∧ e.Minimal := by
  constructor
  · intro g' hg'
    have h := hmin (g'.comp e) (by rw [sign_comp, hg']; exact hsign)
    rw [size_comp, ← hsize] at h
    omega
  · intro e' he'
    have h := hmin (g.comp e') (by rw [sign_comp, he']; exact hsign)
    rw [size_comp, ← hsize] at h
    omega

end Diagram

namespace PortGraph.SimpleCircuit

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem germ_region_hub_card (s : Bool) :
    Fintype.card (C.GermHub s) + Fintype.card (C.InteriorHub (!s)) = Fintype.card C.ComponentHub := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
    C.germ_region_hub_sum hEuler s (fun _ => (1 : Nat))

include hEuler in
theorem germ_region_witnesses_minimal
    (d : Diagram P [] []) (hmin : d.Minimal)
    (hsize : Fintype.card G.Hub = d.size) (hsign : G.sign = d.sign)
    (hconn : ∀ h k : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl k)))
    (s : Bool) (g : Diagram P [] (C.frontierWord (!s))) (e : Diagram P (C.frontierWord (!s)) [])
    (hgs : g.size = Fintype.card (C.GermHub s))
    (hes : e.size = Fintype.card (C.InteriorHub (!s)))
    (hg : g.sign = (C.germGraph hEuler s).sign) (he : e.sign = (C.regionGraph hEuler (!s)).sign) :
    g.Minimal ∧ e.Minimal := by
  by_cases hex : Nonempty C.ComponentHub
  · have hcard : Fintype.card C.ComponentHub = Fintype.card G.Hub := by
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
        C.component_hub_sum_of_connected hconn hex (fun _ => (1 : Nat))
    apply d.minimal_closed_factors hmin g e
    · rw [hgs, hes, C.germ_region_hub_card hEuler, hcard, hsize]
    · rw [hg, he, C.germGraph_region_sign hEuler]
      exact (C.component_hub_sum_of_connected hconn hex
        (fun h => P.parity (G.hubLabel h))).trans hsign
  · let : IsEmpty C.ComponentHub := not_nonempty_iff.mp hex
    let : IsEmpty (C.GermHub s) := ⟨fun h => by
      have hc : C.InCircuitComponent (.inr (.inl h.val)) := by
        rcases h.property with hc | hi
        · exact C.circuitVertex_in_component hc
        · exact C.interiorVertex_in_component hi
      exact isEmptyElim (⟨h.val, hc⟩ : C.ComponentHub)⟩
    let : IsEmpty (C.InteriorHub (!s)) := ⟨fun h =>
      isEmptyElim (⟨h.val, C.interiorVertex_in_component h.property⟩ : C.ComponentHub)⟩
    have hg0 : g.size = 0 := hgs.trans Fintype.card_of_isEmpty
    have he0 : e.size = 0 := hes.trans Fintype.card_of_isEmpty
    exact ⟨fun _ _ => hg0 ▸ Nat.zero_le _, fun _ _ => he0 ▸ Nat.zero_le _⟩

end PortGraph.SimpleCircuit

namespace Smoothing

variable {d : Diagram P [] []} {H : PortGraph P [] []} {circles : List S}
    (t : Smoothing d.graph H circles)

theorem exists_minimal_circuit_diagrams (hmin : d.Minimal) (hs : d.sign = 1)
    (hn : ∀ h : d.graph.Hub, 0 < (P.word (d.graph.hubLabel h)).length)
    (C : H.SimpleCircuit) (s : Bool) :
    ∃ g : Diagram P [] (C.frontierWord (!s)), ∃ e : Diagram P (C.frontierWord (!s)) [],
      (g.labels : Multiset R) = (∑ h : C.GermHub s, ([H.hubLabel h.val] : Multiset R)) ∧
      (e.labels : Multiset R) = (∑ h : C.InteriorHub (!s), ([H.hubLabel h.val] : Multiset R)) ∧
      g.size = Fintype.card (C.GermHub s) ∧ e.size = Fintype.card (C.InteriorHub (!s)) ∧
      g.sign = (C.germGraph (t.diagram_dualEuler hn) s).sign ∧
      e.sign = (C.regionGraph (t.diagram_dualEuler hn) (!s)).sign ∧ g.Minimal ∧ e.Minimal := by
  obtain ⟨g, hgl, hgs, hg⟩ := C.exists_germ_diagram_preserving (t.diagram_dualEuler hn) s
    (fun h => t.hub_word_nonempty hn h.val)
  obtain ⟨e, hel, hes, he⟩ := C.exists_region_diagram_preserving (t.diagram_dualEuler hn) (!s)
    (fun h => t.hub_word_nonempty hn h.val)
  have hm := C.germ_region_witnesses_minimal (t.diagram_dualEuler hn) d hmin
    (t.hub_card.trans d.graph_hub_card) (t.sign.trans d.graph_sign)
    (t.minimal_odd_hubs_reachable hmin hs hn) s g e hgs hes hg he
  exact ⟨g, e, hgl, hel, hgs, hes, hg, he, hm⟩

end Smoothing
end ThomGame.Pictures
