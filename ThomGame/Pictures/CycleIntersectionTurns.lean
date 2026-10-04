module

public import ThomGame.Pictures.CycleGermQuadNeighbourhood
public import ThomGame.Pictures.CircuitGermBoundary

/-!
# Local turns between cubic cycles with at most one shared edge label

At a cycle hub there is exactly one non-rim slot, so rotating from that
slot enters the rim. At a common edge of two cycles, a continuing turn
along the second cycle must leave the first cycle. These are the local
incidence facts behind the three-edge paths in Proposition 9.9.
-/

@[expose] public section
namespace ThomGame

namespace Hypergraph.Cycle

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (C : Cycle A.hypergraph)

theorem empty_boundary_no_rim : ∀ s ∈ ([] : List S), s ∉ Set.range C.edge :=
  fun _ h => False.elim (List.not_mem_nil h)

theorem row_nonrim_unique (v : Fin C.length) (j k : Fin 3)
    (hj : A.column (C.vertex v) j ∉ Set.range C.edge)
    (hk : A.column (C.vertex v) k ∉ Set.range C.edge) : j = k := by
  classical
  have hc : Fintype.card {i : Fin 3 // A.column (C.vertex v) i ∉ Set.range C.edge} ≤ 1 := by
    rw [Fintype.card_subtype_compl, C.row_rim_card, Fintype.card_fin]
  exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨j, hj⟩ ⟨k, hk⟩)

end Hypergraph.Cycle

namespace Pictures.PortGraph

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]

omit [DecidableEq R] [DecidableEq S] in
theorem row_label_injective_at_vertex {x y : G.Dart} (hv : x.vertex = y.vertex)
    (hl : Port.label G.jointLabel x = Port.label G.jointLabel y) : x = y := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j b => exact isEmptyElim j
  | hub h j =>
    cases y with
    | top k => exact k.elim0
    | bottom k => exact k.elim0
    | joint k b => exact isEmptyElim k
    | hub k l =>
      have hh : h = k := Sum.inl.inj (Sum.inr.inj hv)
      subst k
      have hl' := (SolutionGroup.rowGraph_port_label A G h j).symm.trans
        (hl.trans (SolutionGroup.rowGraph_port_label A G h l))
      exact congrArg (fun k : Fin 3 => (Port.hub h k : G.Dart)) (A.column_injective _ hl')

omit [DecidableEq R] [DecidableEq S] in
theorem row_rotation_ne_self (x : G.Dart) : G.rotation x ≠ x := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j b => exact isEmptyElim j
  | hub h j =>
    change (Port.hub h (G.hubRotation h j) : G.Dart) ≠ .hub h j
    have hn : G.hubRotation h j ≠ j := by
      change (if G.hubFlip h then (finRotate 3).symm else finRotate 3) j ≠ j
      have hf : ∀ (b : Bool) (i : Fin 3),
          (if b then (finRotate 3).symm else finRotate 3) i ≠ i := by decide +kernel
      exact hf (G.hubFlip h) j
    intro he
    exact hn (by simpa only [Port.hub.injEq, heq_eq_eq, true_and] using he)

omit [DecidableEq R] [DecidableEq S] in
theorem row_twin_vertex_ne (x : G.Dart) : (G.pairing.twin x).vertex ≠ x.vertex := by
  intro hv
  exact G.pairing.ne_self x (G.row_label_injective_at_vertex hv (G.pairing.label_twin x))

variable (C D : Hypergraph.Cycle A.hypergraph)
  (hcommon : ∀ e f, e ∈ Set.range C.edge → e ∈ Set.range D.edge →
    f ∈ Set.range C.edge → f ∈ Set.range D.edge → e = f)

include hcommon in
theorem common_cycle_ports_eq {x y : G.Dart} (hv : x.vertex = y.vertex)
    (hxC : Port.label G.jointLabel x ∈ Set.range C.edge)
    (hxD : Port.label G.jointLabel x ∈ Set.range D.edge)
    (hyC : Port.label G.jointLabel y ∈ Set.range C.edge)
    (hyD : Port.label G.jointLabel y ∈ Set.range D.edge) : x = y :=
  G.row_label_injective_at_vertex hv (hcommon _ _ hxC hxD hyC hyD)

include hcommon in
theorem continuing_common_edge_leaves_first (x : G.Dart)
    (hxC : Port.label G.jointLabel x ∈ Set.range C.edge)
    (hxD : Port.label G.jointLabel x ∈ Set.range D.edge)
    (hyD : Port.label G.jointLabel (G.circuitStep x) ∈ Set.range D.edge) :
    Port.label G.jointLabel (G.circuitStep x) ∉ Set.range C.edge := by
  intro hyC
  have hxCt : Port.label G.jointLabel (G.pairing.twin x) ∈ Set.range C.edge := by
    rw [G.pairing.label_twin]; exact hxC
  have hxDt : Port.label G.jointLabel (G.pairing.twin x) ∈ Set.range D.edge := by
    rw [G.pairing.label_twin]; exact hxD
  exact G.row_rotation_ne_self (G.pairing.twin x)
    (G.common_cycle_ports_eq C D hcommon (G.vertex_circuitStep x) hyC hyD hxCt hxDt)

theorem rotation_nonrim_enters_rim (a : G.RimDart C) (x : G.Dart)
    (hv : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex x.vertex)
    (hx : Port.label G.jointLabel x ∉ Set.range C.edge) :
    Port.label G.jointLabel (G.rotation x) ∈ Set.range C.edge := by
  classical
  by_contra hn
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j b => exact isEmptyElim j
  | hub h j =>
    obtain ⟨k, hk⟩ := G.rimSimpleCircuit_hub_label C a h hv
    have hx' : A.column (C.vertex k) j ∉ Set.range C.edge := by
      rw [hk]
      rwa [SolutionGroup.rowGraph_port_label A G h j] at hx
    have hn' : A.column (C.vertex k) (G.hubRotation h j) ∉ Set.range C.edge := by
      rw [hk]
      rwa [G.rotation_hub, SolutionGroup.rowGraph_port_label A G h (G.hubRotation h j)] at hn
    have he := C.row_nonrim_unique k (G.hubRotation h j) j hn' hx'
    exact G.row_rotation_ne_self (.hub h j) (congrArg (fun z : Fin 3 => (Port.hub h z : G.Dart)) he)

omit [IsEmpty G.Joint] in
theorem rimSimpleCircuit_marked_label (a : G.RimDart C) {x : G.Dart}
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x) :
    Port.label G.jointLabel x ∈ Set.range C.edge := by
  obtain ⟨⟨i, side⟩, rfl⟩ := hx
  cases side
  · exact G.rimSimpleCircuit_rim C (by simp) (by simp) a i
  · change Port.label G.jointLabel (G.pairing.twin _) ∈ _
    rw [G.pairing.label_twin]
    exact G.rimSimpleCircuit_rim C (by simp) (by simp) a _

omit [IsEmpty G.Joint] in
theorem rimSimpleCircuit_marked_of_vertex_label (a : G.RimDart C) {x : G.Dart}
    (hv : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).OnCircuitVertex x.vertex)
    (hx : Port.label G.jointLabel x ∈ Set.range C.edge) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked x :=
  G.rimSimpleCircuit_marked_of_component C (by simp) (by simp) a ⟨x, hx⟩
    (G.rimSimpleCircuit_component_of_vertex C (by simp) (by simp) a ⟨x, hx⟩ hv)

theorem frontier_rotation_marked (a : G.RimDart C) {s : Bool} {x : G.Dart}
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s x) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Marked (G.rotation x) := by
  have hv := ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).exists_frontier_iff x).mp ⟨s, hx⟩
  apply G.rimSimpleCircuit_marked_of_vertex_label C a
  · rw [G.vertex_rotation]; exact hv.1
  · exact G.rotation_nonrim_enters_rim C a x hv.1
      (G.rimSimpleCircuit_frontier_not_rim C (by simp) (by simp) a s x hx)

include hcommon in
theorem frontier_common_edge_exits (a : G.RimDart C) {s : Bool} {x : G.Dart}
    (hx : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s x)
    (hyD : Port.label G.jointLabel (G.rotation x) ∈ Set.range D.edge)
    (hzD : Port.label G.jointLabel (G.circuitStep (G.rotation x)) ∈ Set.range D.edge) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).Frontier s
      (G.circuitStep (G.rotation x)) := by
  let γ := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  have hm := G.frontier_rotation_marked C a hx
  have hn := G.continuing_common_edge_leaves_first C D hcommon (G.rotation x)
    (G.rimSimpleCircuit_marked_label C a hm) hyD hzD
  have hn' : ¬ γ.Marked (G.circuitStep (G.rotation x)) :=
    fun h => hn (G.rimSimpleCircuit_marked_label C a h)
  have hs₁ : γ.Sector (!s) (G.pairing.twin (G.rotation x)) := by
    have hs := γ.sector_next hx.1
    change γ.Sector (!s) (γ.edgeTwist (G.rotation x)) at hs
    rwa [γ.edgeTwist_of_marked hm] at hs
  have hs₂ := γ.sector_next hs₁
  change γ.Sector (!s) (γ.edgeTwist (G.circuitStep (G.rotation x))) at hs₂
  rw [γ.edgeTwist_of_unmarked _ hn'] at hs₂
  exact ⟨hs₂, hn'⟩

end Pictures.PortGraph
end ThomGame
