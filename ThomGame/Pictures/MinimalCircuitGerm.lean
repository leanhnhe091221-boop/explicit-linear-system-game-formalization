module

public import ThomGame.Pictures.DiagramComponentExtraction
public import ThomGame.Pictures.CircuitGermCharge
public import ThomGame.Pictures.DiagramCircuitSeparation

/-!
# Zero-sign germs of minimal odd diagrams

The component condition in the germ parity argument follows from actual
diagram minimality whenever the circuit component contains a relation hub.
If it contains no relation hub, its germs already have zero sign. Thus no
placement of unrelated components inside or outside a circuit is needed.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

variable {u v : List S} {G : PortGraph P u v}

theorem exists_dart_of_reachable {x y : G.Vertex} (h : G.Reachable x y)
    (hx : ∃ a : G.Dart, a.vertex = x) : ∃ a : G.Dart, a.vertex = y := by
  induction h with
  | refl => exact hx
  | tail _ hxy _ => obtain ⟨a, _, ha⟩ := hxy; exact ⟨G.pairing.twin a, ha⟩

namespace SimpleCircuit

variable (C : G.SimpleCircuit)

theorem inCircuitComponent_iff_reachable (x : G.Vertex) :
    C.InCircuitComponent x ↔ G.Reachable x C.cutBase.vertex := by
  constructor
  · rintro ⟨a, ha, hc⟩
    have hr := G.connected_vertex_reachable
      ((RotationEuler.connected_swap_iff G.circuitStep G.pairing.perm _ _).mp hc)
    exact ha ▸ hr
  · intro hr
    obtain ⟨a, ha⟩ := exists_dart_of_reachable (G.reachable_symm hr) ⟨C.cutBase, rfl⟩
    exact ⟨a, ha, (RotationEuler.connected_swap_iff G.circuitStep G.pairing.perm _ _).mpr
      (G.reachable_connects_darts hr a C.cutBase ha rfl)⟩

theorem inCircuitComponent_iff_graphComponent (x : G.Vertex) :
    C.InCircuitComponent x ↔ G.graphComponent x = G.graphComponent C.cutBase.vertex :=
  (C.inCircuitComponent_iff_reachable x).trans (G.graphComponent_eq_iff _ _).symm

theorem all_hubs_in_component
    (hconn : ∀ h j : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl j)))
    (hex : Nonempty C.ComponentHub) :
    ∀ h : G.Hub, C.InCircuitComponent (.inr (.inl h)) := by
  obtain ⟨⟨j, hj⟩⟩ := hex
  intro h
  exact (C.inCircuitComponent_iff_reachable _).mpr
    ((hconn h j).trans ((C.inCircuitComponent_iff_reachable _).mp hj))

theorem component_hub_sum_of_connected {B : Type*} [AddCommMonoid B]
    (hconn : ∀ h j : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl j)))
    (hex : Nonempty C.ComponentHub) (weight : G.Hub → B) :
    (∑ h : C.ComponentHub, weight h.val) = ∑ h : G.Hub, weight h := by
  rw [subtype_sum_indicator]
  simp only [C.all_hubs_in_component hconn hex, ite_true]

end SimpleCircuit

namespace SimpleCircuit

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem germGraph_sign_of_no_component_hubs (hn : IsEmpty C.ComponentHub) (s : Bool) :
    (C.germGraph hEuler s).sign = 0 := by
  change (∑ h : C.GermHub s, P.parity (G.hubLabel h.val)) = 0
  apply Finset.sum_eq_zero
  intro h _
  have hc : C.InCircuitComponent (.inr (.inl h.val)) := by
    rcases h.property with hh | hh
    · exact C.circuitVertex_in_component hh
    · exact C.interiorVertex_in_component hh
  exact (hn.false ⟨h.val, hc⟩).elim

include hEuler in
theorem exists_germ_sign_zero_of_hubs_reachable
    (hconn : ∀ h j : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl j)))
    (hs : G.sign = 1)
    (hCircuit : (∑ h : C.CircuitHub, P.parity (G.hubLabel h.val)) = 0) :
    ∃ s, (C.germGraph hEuler s).sign = 0 := by
  by_cases hex : Nonempty C.ComponentHub
  · apply C.exists_germGraph_sign_zero hEuler hCircuit
    exact (C.component_hub_sum_of_connected hconn hex (fun h => P.parity (G.hubLabel h))).trans hs
  · exact ⟨false, C.germGraph_sign_of_no_component_hubs hEuler (not_nonempty_iff.mp hex) false⟩

end SimpleCircuit
end PortGraph

namespace Diagram

variable (d : Diagram P [] [])

theorem minimal_odd_circuit_exists_germ_sign_zero (hmin : d.Minimal) (hs : d.sign = 1)
    (C : d.graph.SimpleCircuit)
    (hCircuit : (∑ h : C.CircuitHub, P.parity (d.graph.hubLabel h.val)) = 0) :
    ∃ s, (C.germGraph d.graph_dualEuler s).sign = 0 :=
  C.exists_germ_sign_zero_of_hubs_reachable d.graph_dualEuler
    (d.minimal_odd_hubs_reachable hmin hs) (d.graph_sign.trans hs) hCircuit

end Diagram
end ThomGame.Pictures
