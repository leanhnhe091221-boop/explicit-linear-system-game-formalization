module

public import ThomGame.Pictures.CircuitGermGraph
public import ThomGame.Pictures.BoundarySwapGraph
public import ThomGame.Pictures.BoundaryQuadPath

/-!
# Outer-quadrilateral hubs belong to the original circuit

Each boundary leaf in the actual germ is paired with an outward port at
a circuit vertex. Consequently, both internal hubs of a boundary
quadrilateral come from the original circuit. This fact supplies the
local incidence information needed to fix their labels under retraction.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

theorem germInternalPort_swapBoundary_hub
    (a : {a : G.Dart // C.GermVertex s a.vertex}) (h : C.GermHub s)
    (hv : ((C.germGraph hEuler s).swapBoundaryPorts (C.germInternalPort hEuler s a)).vertex =
      .inr (.inl h)) : a.val.vertex = .inr (.inl h.val) := by
  rcases a with ⟨a, ha⟩
  cases a with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub k j =>
    rw [C.germInternalPort_hub hEuler s ⟨k, ha⟩] at hv
    have hk : (⟨k, ha⟩ : C.GermHub s) = h := Sum.inl.inj (Sum.inr.inj hv)
    exact congrArg (fun k : G.Hub => (Sum.inr (Sum.inl k) : G.Vertex)) (congrArg Subtype.val hk)
  | joint k b =>
    rw [C.germInternalPort_joint hEuler s ⟨k, ha⟩] at hv
    cases hv

theorem germGraph_swapBoundary_twin_top_onCircuit
    (j : Fin (C.frontierWord (!s)).length) (h : C.GermHub s)
    (hh : ((C.germGraph hEuler s).swapBoundary.pairing.twin (.top j)).vertex = .inr (.inl h)) :
    C.OnCircuitVertex (.inr (.inl h.val)) := by
  have hp := (C.germGraph hEuler s).swapBoundary_pairing (.bottom j)
  change (C.germGraph hEuler s).swapBoundary.pairing.twin (.top j) =
    (C.germGraph hEuler s).swapBoundaryPorts ((C.germGraph hEuler s).pairing.twin (.bottom j)) at hp
  rw [C.germGraph_twin_bottom] at hp
  have he : ((C.germGraph hEuler s).swapBoundaryPorts
      (C.germInternalPort hEuler s ⟨(C.boundaryEnumeration (!s) j).val,
        (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr (C.boundaryEnumeration (!s) j).property)⟩)).vertex =
        .inr (.inl h) := (congrArg Port.vertex hp).symm.trans hh
  have hv := ((C.exists_frontier_iff _).mp ⟨!s, (C.boundaryEnumeration (!s) j).property⟩).1
  rwa [C.germInternalPort_swapBoundary_hub hEuler s _ h he] at hv

theorem germQuad_firstHub_onCircuit
    (q : (C.germGraph hEuler s).swapBoundary.BoundaryQuadPath) :
    C.OnCircuitVertex (.inr (.inl q.firstHub.val)) := by
  have hv := q.first_twin_vertex
  cases he : q.start with
  | inl j =>
    change ((C.germGraph hEuler s).swapBoundary.pairing.twin
      ((C.germGraph hEuler s).swapBoundary.boundaryDart q.start)).vertex = _ at hv
    rw [he] at hv
    exact C.germGraph_swapBoundary_twin_top_onCircuit hEuler s j q.firstHub hv
  | inr j => exact j.elim0

theorem germQuad_secondHub_onCircuit
    (q : (C.germGraph hEuler s).swapBoundary.BoundaryQuadPath) :
    C.OnCircuitVertex (.inr (.inl q.secondHub.val)) := by
  have hv : ((C.germGraph hEuler s).swapBoundary.pairing.twin
      ((C.germGraph hEuler s).swapBoundary.boundaryDart q.finish)).vertex = .inr (.inl q.secondHub) := by
    rw [← q.last_twin, (C.germGraph hEuler s).swapBoundary.pairing.involutive]
    rfl
  cases he : q.finish with
  | inl j =>
    rw [he] at hv
    exact C.germGraph_swapBoundary_twin_top_onCircuit hEuler s j q.secondHub hv
  | inr j => exact j.elim0

end ThomGame.Pictures.PortGraph.SimpleCircuit
