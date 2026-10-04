module

public import ThomGame.Pictures.CoveredRimSides

/-!
# Covered restrictions of a rim have a common external side on each component

The restricted adjacency uses the original marked darts and their actual
edge twins, retaining only labels in the chosen set. Its equivalence
closure is genuine finite graph connectivity. Facial covers from an
intersecting family give distinct endpoint labels on every retained edge
and propagate the external frontier side across every connected component.
This is the closed row-graph form of Slofstra Lemma 11.10.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def RestrictedAdj (E : Set S) (x y : {v : G.Vertex // C.OnCircuitVertex v}) : Prop :=
  ∃ a : G.Dart, C.Marked a ∧ Port.label G.jointLabel a ∈ E ∧
    a.vertex = x.val ∧ (G.pairing.twin a).vertex = y.val

def RestrictedConnected (E : Set S) :
    {v : G.Vertex // C.OnCircuitVertex v} → {v : G.Vertex // C.OnCircuitVertex v} → Prop :=
  Relation.EqvGen (C.RestrictedAdj E)

theorem restrictedAdj_symm (E : Set S) {x y : {v : G.Vertex // C.OnCircuitVertex v}}
    (h : C.RestrictedAdj E x y) : C.RestrictedAdj E y x := by
  obtain ⟨a, hm, he, hx, hy⟩ := h
  exact ⟨G.pairing.twin a, (C.marked_twin_iff a).mpr hm,
    (G.pairing.label_twin a).symm ▸ he, hy, (congrArg Port.vertex (G.pairing.involutive a)).trans hx⟩

end SimpleCircuit

open scoped Classical

variable {R S I : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C)

theorem rim_exists_unmarked_at_vertex (v : G.Vertex)
    (hv : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex v) :
    ∃ x : G.Dart, x.vertex = v ∧ ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  obtain ⟨i, rfl⟩ := hv
  obtain ⟨h, p, hp⟩ := exists_hub_dart (γ.dart i)
  have hhv : γ.OnCircuitVertex (.inr (.inl h)) := ⟨i, congrArg Port.vertex hp⟩
  obtain ⟨j, hj⟩ := G.rimSimpleCircuit_hub_label C a h hhv
  have hex : ∃ q : Fin 3, A.column (C.vertex j) q ∉ Set.range C.edge := by
    by_contra hn
    push Not at hn
    have hc := C.row_rim_card j
    simp only [hn, Fintype.card_subtype_true, Fintype.card_fin] at hc
    omega
  obtain ⟨q, hq⟩ := hex
  refine ⟨.hub h q, (congrArg Port.vertex hp).symm, ?_⟩
  intro hm
  have he := G.rimSimpleCircuit_marked_label C a hm
  rw [SolutionGroup.rowGraph_port_label, ← hj] at he
  exact hq he

variable (E : Set S) (Φ : I → Hypergraph.Cycle A.hypergraph)
  (hcommon : ∀ i e f, e ∈ Set.range C.edge → e ∈ Set.range (Φ i).edge →
    f ∈ Set.range C.edge → f ∈ Set.range (Φ i).edge → e = f)
  (hcovered : ∀ e ∈ E, ∃ i, e ∈ Set.range (Φ i).edge)
  (hfaces : ∀ i (b : G.RimDart (Φ i)),
    ∃ side, (G.rimSimpleCircuit (Φ i) ((Φ i).empty_boundary_no_rim) ((Φ i).empty_boundary_no_rim) b).BoundsFaceOrbit side)

include hcommon hcovered hfaces in
theorem covered_rim_edge_frontier_iff (x p q : G.Dart)
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x)
    (he : Port.label G.jointLabel x ∈ E)
    (hpv : p.vertex = x.vertex) (hqv : q.vertex = (G.pairing.twin x).vertex)
    (hp : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked p)
    (hq : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked q) (s : Bool) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s p ↔
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s q := by
  obtain ⟨i, hi⟩ := hcovered _ he
  let b : G.RimDart (Φ i) := ⟨x, hi⟩
  obtain ⟨side, hf⟩ := hfaces i b
  have hb : (G.rimSimpleCircuit (Φ i) ((Φ i).empty_boundary_no_rim) ((Φ i).empty_boundary_no_rim) b).Marked x := by
    refine ⟨(0, false), ?_⟩
    exact congrArg Subtype.val (OrbitEnumeration.dart_zero (G.rimWalk (Φ i) ((Φ i).empty_boundary_no_rim) ((Φ i).empty_boundary_no_rim)) b)
  exact G.rim_shared_face_frontier_iff C a (Φ i) b (hcommon i) side hf x p q hx hb hpv hqv hp hq s

include hcommon hcovered hfaces in
theorem covered_rim_connected_frontier_iff
    {v w : {v : G.Vertex // (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex v}}
    (hvw : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).RestrictedConnected E v w)
    (p q : G.Dart) (hpv : p.vertex = v.val) (hqv : q.vertex = w.val)
    (hp : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked p)
    (hq : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked q) (s : Bool) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s p ↔
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s q := by
  induction hvw generalizing p q with
  | rel v w he =>
    obtain ⟨x, hx, he, hxv, hxw⟩ := he
    exact G.covered_rim_edge_frontier_iff C a E Φ hcommon hcovered hfaces x p q hx he
      (hpv.trans hxv.symm) (hqv.trans hxw.symm) hp hq s
  | refl v =>
    have he := G.rim_unmarked_same_vertex_eq C a (hpv.symm ▸ v.property)
      (hpv.trans hqv.symm) hp hq
    exact he ▸ Iff.rfl
  | symm v w _ ih => exact (ih q p hqv hpv hq hp).symm
  | trans v w z _ _ ih ik =>
    obtain ⟨r, hrv, hr⟩ := G.rim_exists_unmarked_at_vertex C a w.val w.property
    exact (ih p r hpv hrv hp hr).trans (ik r q hrv hqv hr hq)

include hcommon hcovered hfaces in
theorem covered_rim_component_common_side
    (v : {v : G.Vertex // (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex v}) :
    ∃ s, ∀ w : {v : G.Vertex // (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex v},
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).RestrictedConnected E v w →
      ∀ q : G.Dart, q.vertex = w.val → ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked q →
        (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s q := by
  obtain ⟨p, hpv, hp⟩ := G.rim_exists_unmarked_at_vertex C a v.val v.property
  obtain ⟨s, hs⟩ := ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).exists_frontier_iff p).mpr
    ⟨hpv.symm ▸ v.property, hp⟩
  exact ⟨s, fun w hvw q hqv hq =>
    (G.covered_rim_connected_frontier_iff C a E Φ hcommon hcovered hfaces hvw p q hpv hqv hp hq s).mp hs⟩

omit [IsEmpty G.Joint] in
include hcovered in
theorem covered_rim_edges_have_distinct_labels
    (hc : ∀ i (b : G.RimDart (Φ i)), (G.rimSimpleCircuit (Φ i) ((Φ i).empty_boundary_no_rim) ((Φ i).empty_boundary_no_rim) b).IsLabelCover)
    (x : G.Dart) (hx : Port.label G.jointLabel x ∈ E) : G.EdgeHasDistinctHubLabels x := by
  obtain ⟨i, hi⟩ := hcovered _ hx
  exact rim_cover_edge (Φ i) (hc i) x hi

end ThomGame.Pictures.PortGraph
