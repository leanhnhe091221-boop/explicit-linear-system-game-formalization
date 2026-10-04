module

public import ThomGame.Construction.WheelGraph
public import ThomGame.Pictures.MinimalStateRimGerm

/-!
# Diagram witnesses for actual closed Sigma graphs

Only Euler saturation, hub count and sign connect the actual graph to
the diagram witness. No graph isomorphism or smoothing is required.
Minimal odd witnesses imply the actual graph state, whose connectivity
and minimal circuit-region witnesses have already been proved.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

abbrev SigmaMinimalState (H : SigmaGraph [] []) : Prop := H.ClosedMinimalOddState

structure SigmaGraphWitness (d : SigmaDiagram [] []) (H : SigmaGraph [] []) : Prop where
  euler : eulerDefect H.pairing.perm H.circuitStep = 0
  size_eq : Fintype.card H.Hub = d.size
  sign_eq : H.sign = d.sign

namespace SigmaGraphWitness

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []}

theorem ofSmoothing {circles : List (Fin 1889684)} (t : Smoothing d.graph H circles) :
    SigmaGraphWitness d H where
  euler := t.diagram_eulerDefect (fun _ => by change 0 < 3; omega)
  size_eq := t.hub_card.trans d.graph_hub_card
  sign_eq := t.sign.trans d.graph_sign

instance {circles : List (Fin 1889684)} :
    CoeOut (Smoothing d.graph H circles) (SigmaGraphWitness d H) := ⟨ofSmoothing⟩

theorem ofDiagram (d : SigmaDiagram [] []) : SigmaGraphWitness d d.graph :=
  ofSmoothing (.refl d.graph)

variable (t : SigmaGraphWitness d H)

include t in
theorem dualEuler : RotationEuler.count H.circuitStep H.pairing.perm =
    2 * Nat.card (Component H.circuitStep H.pairing.perm) :=
  H.dualEuler_eq_twice_components t.euler

include t in
theorem hub_card : Fintype.card H.Hub = Fintype.card d.graph.Hub :=
  t.size_eq.trans d.graph_hub_card.symm

include t in
theorem sign : H.sign = d.graph.sign := t.sign_eq.trans d.graph_sign.symm

include t in
theorem minimalState (hmin : d.Minimal) (hs : d.sign = 1) : SigmaMinimalState H :=
  PortGraph.ClosedMinimalOddState.of_witness t.euler (t.sign_eq.trans hs) d hmin t.size_eq.symm hs

include t in
theorem minimal_odd_hubs_reachable (hmin : d.Minimal) (hs : d.sign = 1)
    (x y : H.Hub) : H.Reachable (.inr (.inl x)) (.inr (.inl y)) :=
  (t.minimalState hmin hs).hubs_reachable (fun _ => by change 0 < 3; omega) x y

include t in
theorem minimal_odd_reduced_reachable [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1) :
    ∀ x y : H.Vertex, H.Reachable x y :=
  (t.minimalState hmin hs).vertices_reachable (fun _ => by change 0 < 3; omega)

noncomputable def minimal_odd_recoveredAllPorts [IsEmpty H.Joint]
    (hmin : d.Minimal) (hs : d.sign = 1) (C : H.SimpleCircuit) (s : Bool) :
    (C.germReduction t.dualEuler s).graph.Dart ≃ H.Dart :=
  C.recoveredAllPorts t.dualEuler (t.minimal_odd_reduced_reachable hmin hs) s

theorem exists_minimal_circuit_diagrams (hmin : d.Minimal) (hs : d.sign = 1)
    (C : H.SimpleCircuit) (s : Bool) :
    ∃ g : SigmaDiagram [] (C.frontierWord (!s)), ∃ e : SigmaDiagram (C.frontierWord (!s)) [],
      (g.labels : Multiset (Fin 1417152)) =
        (∑ x : C.GermHub s, ([H.hubLabel x.val] : Multiset (Fin 1417152))) ∧
      (e.labels : Multiset (Fin 1417152)) =
        (∑ x : C.InteriorHub (!s), ([H.hubLabel x.val] : Multiset (Fin 1417152))) ∧
      g.size = Fintype.card (C.GermHub s) ∧ e.size = Fintype.card (C.InteriorHub (!s)) ∧
      g.sign = (C.germGraph t.dualEuler s).sign ∧ e.sign = (C.regionGraph t.dualEuler (!s)).sign ∧
      g.Minimal ∧ e.Minimal :=
  (t.minimalState hmin hs).exists_minimal_circuit_diagrams (fun _ => by change 0 < 3; omega) C s

theorem minimal_odd_stellar_rim_hasZeroSignGerm (hmin : d.Minimal) (hs : d.sign = 1)
    (C : Hypergraph.Cycle numberedSystem.hypergraph) (a : H.RimDart C)
    (hc : C.Stellar numberedSystem.rhs) : H.RimHasZeroSignGerm C t.dualEuler a := by
  obtain ⟨s, _, _, _, _, _, hzero⟩ :=
    (t.minimalState hmin hs).exists_minimal_stellar_rim_germ C a hc
  exact ⟨s, hzero⟩

end SigmaGraphWitness

namespace SigmaMinimalState

variable {H : SigmaGraph [] []} (h : SigmaMinimalState H)

include h in
theorem exists_graph_witness :
    ∃ d : SigmaDiagram [] [], d.Minimal ∧ d.sign = 1 ∧ SigmaGraphWitness d H := by
  obtain ⟨d, _, hsize, hsign, hmin⟩ := h.exists_minimal_diagram (fun _ => by change 0 < 3; omega)
  exact ⟨d, hmin, hsign, ⟨h.euler, hsize.symm, h.sign.trans hsign.symm⟩⟩

end SigmaMinimalState
end ThomGame.Construction
