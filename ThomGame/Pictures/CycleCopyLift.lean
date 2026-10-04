module

public import ThomGame.Pictures.CircuitCopyEdges

/-!
# Actual port lifts of a copied hypergraph cycle

A label copy supplies one actual hub over every base vertex. Equal-labelled
rim ports at two different base vertices are paired in the original graph.
The lift also contains the hub of the original seed dart. These statements
retain the actual pairing, rather than only the cardinality of a copy.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []}

structure CycleCopyLift (G : SolutionGroup.RowGraph A [] [])
    (γ : Hypergraph.Cycle A.hypergraph) where
  hub : Fin γ.length → G.Hub
  label : ∀ i, G.hubLabel (hub i) = γ.vertex i
  twin : ∀ (i j : Fin γ.length) (p q : Fin 3), i ≠ j →
    A.column (γ.vertex i) p ∈ Set.range γ.edge →
    A.column (γ.vertex i) p = A.column (γ.vertex j) q →
    G.pairing.twin (.hub (hub i) p) = .hub (hub j) q

namespace CycleCopyLift

variable {γ : Hypergraph.Cycle A.hypergraph} (L : G.CycleCopyLift γ)

theorem hub_injective : Function.Injective L.hub := by
  intro i j hij
  exact γ.vertex.injective ((L.label i).symm.trans
    ((congrArg G.hubLabel hij).trans (L.label j)))

theorem hub_eq_of_label {h : G.Hub} (hh : h ∈ Set.range L.hub)
    (i : Fin γ.length) (hi : G.hubLabel h = γ.vertex i) : L.hub i = h := by
  obtain ⟨j, rfl⟩ := hh
  exact congrArg L.hub (γ.vertex.injective (hi.symm.trans (L.label j)))

end CycleCopyLift

variable [IsEmpty G.Joint]

namespace SimpleCircuit

variable (C : G.SimpleCircuit) (γ : Hypergraph.Cycle A.hypergraph)
  (hl : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)
  (hc : C.IsLabelCopy)

noncomputable def copyHub (i : Fin γ.length) : G.Hub :=
  C.hubAt ((C.copyVertexEquiv γ hl hc).symm i)

theorem copyHub_label (i : Fin γ.length) : G.hubLabel (C.copyHub γ hl hc i) = γ.vertex i := by
  simpa only [copyHub, Equiv.apply_symm_apply] using
    (C.copyVertexEquiv_label γ hl hc ((C.copyVertexEquiv γ hl hc).symm i)).symm

theorem copyHub_marked (i : Fin γ.length) (p : Fin 3)
    (hp : A.column (γ.vertex i) p ∈ Set.range γ.edge) :
    C.Marked (.hub (C.copyHub γ hl hc i) p) := by
  have hr : Port.label G.jointLabel (.hub (C.copyHub γ hl hc i) p : G.Dart) ∈ Set.range γ.edge := by
    rw [SolutionGroup.rowGraph_port_label, C.copyHub_label γ hl hc]
    exact hp
  apply C.marked_of_rim_at_vertex γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim hl ⟨_, hr⟩
    ((C.copyVertexEquiv γ hl hc).symm i)
  exact (C.hubAt_vertex _).symm

noncomputable def copyLift : G.CycleCopyLift γ where
  hub := C.copyHub γ hl hc
  label := C.copyHub_label γ hl hc
  twin i j p q hij hp he := by
    have hq : A.column (γ.vertex j) q ∈ Set.range γ.edge := he ▸ hp
    have heq := C.copy_edge_eq_of_marked_label hc
      (C.copyHub_marked γ hl hc i p hp) (C.copyHub_marked γ hl hc j q hq)
      (by simpa only [SolutionGroup.rowGraph_port_label, C.copyHub_label γ hl hc] using he)
    rcases (G.pairing.edge_eq_iff _ _).mp heq with heq | heq
    · have hh : C.copyHub γ hl hc i = C.copyHub γ hl hc j := by
        exact Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex heq))
      exact (hij (γ.vertex.injective ((C.copyHub_label γ hl hc i).symm.trans
        ((congrArg G.hubLabel hh).trans (C.copyHub_label γ hl hc j))))).elim
    · exact (congrArg G.pairing.twin heq).trans (G.pairing.involutive _)

theorem copyLift_hub_range : Set.range (C.copyLift γ hl hc).hub = Set.range C.hubAt := by
  ext h
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(C.copyVertexEquiv γ hl hc).symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨C.copyVertexEquiv γ hl hc i, congrArg C.hubAt
      ((C.copyVertexEquiv γ hl hc).symm_apply_apply i)⟩

end SimpleCircuit

noncomputable def rimCopyLift (γ : Hypergraph.Cycle A.hypergraph) (a : G.RimDart γ)
    (hc : (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).IsLabelCopy) :
    G.CycleCopyLift γ :=
  (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).copyLift γ
    (G.rimSimpleCircuit_rim γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a) hc

theorem rimCopyLift_seed (γ : Hypergraph.Cycle A.hypergraph) (a : G.RimDart γ)
    (hc : (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).IsLabelCopy)
    (h : G.Hub) (p : Fin 3) (ha : a.val = .hub h p) :
    h ∈ Set.range (G.rimCopyLift γ a hc).hub := by
  let C := G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a
  rw [rimCopyLift, C.copyLift_hub_range]
  refine ⟨0, ?_⟩
  have he : C.dart 0 = a.val := congrArg Subtype.val
    (OrbitEnumeration.dart_zero (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim) a)
  exact Sum.inl.inj (Sum.inr.inj ((C.hubAt_vertex 0).symm.trans
    (congrArg Port.vertex (he.trans ha))))

end ThomGame.Pictures.PortGraph
