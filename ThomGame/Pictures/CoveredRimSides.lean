module

public import ThomGame.Pictures.CircuitCoverEdges
public import ThomGame.Pictures.CycleGermFacialSupport
public import ThomGame.Pictures.FacialCircuitMarked

/-!
# A shared facial rim places both external ports on the same cut side

These are the local incidence and side statements in Slofstra Lemma
11.10. They concern actual ports and actual face turns. No planarity
assumption is replaced by a chosen drawing, and no side equality is
included in the definition of covering.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (C : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C)

theorem rim_unmarked_same_vertex_eq {x y : G.Dart}
    (hv : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex x.vertex)
    (hxy : x.vertex = y.vertex)
    (hx : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x)
    (hy : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked y) : x = y := by
  obtain ⟨h, p, rfl⟩ := exists_hub_dart x
  obtain ⟨k, q, rfl⟩ := exists_hub_dart y
  have hhk : h = k := Sum.inl.inj (Sum.inr.inj hxy)
  subst k
  obtain ⟨j, hj⟩ := G.rimSimpleCircuit_hub_label C a h hv
  have hp : A.column (C.vertex j) p ∉ Set.range C.edge := by
    rw [hj, ← SolutionGroup.rowGraph_port_label A G h p]
    exact fun he => hx (G.rimSimpleCircuit_marked_of_vertex_label C a hv he)
  have hq : A.column (C.vertex j) q ∉ Set.range C.edge := by
    rw [hj, ← SolutionGroup.rowGraph_port_label A G h q]
    exact fun he => hy (G.rimSimpleCircuit_marked_of_vertex_label C a hv he)
  exact congrArg (fun i : Fin 3 => (Port.hub h i : G.Dart)) (C.row_nonrim_unique j p q hp hq)

variable (D : Hypergraph.Cycle A.hypergraph) (b : G.RimDart D)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)
  (side : Bool) (hf : (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).BoundsFaceOrbit side)

include hcommon hf in
theorem rim_face_shared_edge_frontiers (x : G.Dart)
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x)
    (hface : G.circuitStep.SameCycle x
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side))) :
    ∃ s, (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s (G.rotation.symm x) ∧
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s (G.circuitStep x) := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let y := G.rotation.symm x
  have hyr : G.rotation y = x := G.rotation.apply_symm_apply x
  have hyv : y.vertex = x.vertex := G.vertex_rotation_symm x
  have hyp : G.circuitStep (G.pairing.twin y) = x := by
    rw [G.circuitStep_apply, G.pairing.involutive]
    exact hyr
  have hyface : G.circuitStep.SameCycle (G.pairing.twin y)
      ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)) := by
    apply Perm.sameCycle_apply_left.mp
    rwa [hyp]
  have hyD : Port.label G.jointLabel y ∈ Set.range D.edge := by
    have he := G.rimFace_label D b side hf hyface
    rwa [G.pairing.label_twin] at he
  have hyn : ¬ γ.Marked y := by
    intro hy
    have he := G.common_cycle_ports_eq C D hcommon hyv
      (G.rimSimpleCircuit_marked_label C a hy) hyD
      (G.rimSimpleCircuit_marked_label C a hx) (G.rimFace_label D b side hf hface)
    exact G.row_rotation_ne_self y (hyr.trans he.symm)
  have hyv' : γ.OnCircuitVertex y.vertex := hyv.symm ▸ γ.marked_onCircuitVertex hx
  obtain ⟨s, hs⟩ := (γ.exists_frontier_iff y).mpr ⟨hyv', hyn⟩
  have hz := G.frontier_common_edge_exits C D hcommon a hs
    (hyr.symm ▸ G.rimFace_label D b side hf hface)
    (hyr.symm ▸ G.rimFace_label D b side hf hface.apply_left)
  exact ⟨s, hs, hyr ▸ hz⟩

include hcommon hf in
theorem rim_shared_face_frontier_iff (x p q : G.Dart)
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x)
    (hxD : (G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).Marked x)
    (hpv : p.vertex = x.vertex) (hqv : q.vertex = (G.pairing.twin x).vertex)
    (hp : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked p)
    (hq : ¬ (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked q) (s : Bool) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s p ↔
      (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s q := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  have step (y p q : G.Dart) (hy : γ.Marked y)
      (hyface : G.circuitStep.SameCycle y
        ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).port (0, side)))
      (hpv : p.vertex = y.vertex) (hqv : q.vertex = (G.pairing.twin y).vertex)
      (hp : ¬ γ.Marked p) (hq : ¬ γ.Marked q) : γ.Frontier s p ↔ γ.Frontier s q := by
    obtain ⟨t, ht, hu⟩ := G.rim_face_shared_edge_frontiers C a D b hcommon side hf y hy hyface
    have hpe : p = G.rotation.symm y := G.rim_unmarked_same_vertex_eq C a
      (hpv.symm ▸ γ.marked_onCircuitVertex hy) (hpv.trans (G.vertex_rotation_symm y).symm) hp ht.2
    have hqe : q = G.circuitStep y := G.rim_unmarked_same_vertex_eq C a
      (hqv.symm ▸ γ.marked_onCircuitVertex ((γ.marked_twin_iff y).mpr hy))
      (hqv.trans (G.vertex_circuitStep y).symm) hq hu.2
    rw [← hpe] at ht
    rw [← hqe] at hu
    exact ⟨fun hs => (γ.frontier_unique hs ht).symm ▸ hu,
      fun hs => (γ.frontier_unique hs hu).symm ▸ ht⟩
  rcases ((G.rimSimpleCircuit D D.empty_boundary_no_rim D.empty_boundary_no_rim b).marked_iff_face_or_twin side hf x).mp hxD with h | h
  · exact step x p q hx h hpv hqv hp hq
  · have hpp : p.vertex = (G.pairing.twin (G.pairing.twin x)).vertex := by
      rw [G.pairing.involutive]
      exact hpv
    exact (step (G.pairing.twin x) q p ((γ.marked_twin_iff x).mpr hx) h hqv hpp hq hp).symm

end ThomGame.Pictures.PortGraph
