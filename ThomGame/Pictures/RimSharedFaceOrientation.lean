module

public import ThomGame.Pictures.RowEdgeSwitchOrientedFaces

/-!
# Opposite facial sides at the shared edge of two base cycles

The at-most-one-common-label condition forces distinct incoming rim
ports. Both cycles being facial then forces opposite local turns.
This determines matching orientations of the two neighbouring rims
at the two actual cut edges in Figure 18.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (γ δ : Hypergraph.Cycle A.hypergraph)
  (hcommon : ∀ e f, e ∈ Set.range γ.edge → e ∈ Set.range δ.edge →
    f ∈ Set.range γ.edge → f ∈ Set.range δ.edge → e = f)

include hcommon in
theorem rimSwitch_shared_ne (x : G.Dart)
    (hx : Port.label G.jointLabel x ∈ Set.range γ.edge)
    (hy : Port.label G.jointLabel x ∈ Set.range δ.edge) :
    (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨x, hx⟩).val ≠
      (G.rimSwitch δ δ.empty_boundary_no_rim δ.empty_boundary_no_rim ⟨x, hy⟩).val := by
  intro he
  have hd : Port.label G.jointLabel (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨x, hx⟩).val ∈
      Set.range δ.edge := he ▸ (G.rimSwitch δ δ.empty_boundary_no_rim δ.empty_boundary_no_rim ⟨x, hy⟩).property
  have hp := G.common_cycle_ports_eq γ δ hcommon
    (G.rimSwitch_vertex γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨x, hx⟩)
    (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨x, hx⟩).property hd hx hy
  exact G.rimSwitch_ne_self γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim ⟨x, hx⟩ (Subtype.ext hp)

include hcommon in
theorem rimCorner_shared_opposite (x : G.Dart)
    (hx : Port.label G.jointLabel x ∈ Set.range γ.edge)
    (hy : Port.label G.jointLabel x ∈ Set.range δ.edge)
    (side other : Bool) (hs : G.RimCorner γ side ⟨x, hx⟩)
    (ht : G.RimCorner δ other ⟨x, hy⟩) : other = !side := by
  have hn := G.rimSwitch_shared_ne γ δ hcommon x hx hy
  cases side <;> cases other
  · exact (hn (G.rotation.injective (hs.trans ht.symm))).elim
  · rfl
  · rfl
  · exact (hn (hs.symm.trans ht)).elim

include hcommon in
theorem rimFaceSide_shared (x : G.Dart)
    (hx : Port.label G.jointLabel x ∈ Set.range γ.edge)
    (hy : Port.label G.jointLabel x ∈ Set.range δ.edge)
    (hγ : ∀ a : G.RimDart γ, ∃ side, (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side)
    (hδ : ∀ a : G.RimDart δ, ∃ side, (G.rimSimpleCircuit δ δ.empty_boundary_no_rim δ.empty_boundary_no_rim a).BoundsFaceOrbit side) :
    G.rimFaceSide δ ⟨x, hy⟩ = !(G.rimFaceSide γ ⟨x, hx⟩) :=
  G.rimCorner_shared_opposite γ δ hcommon x hx hy _ _
    (G.rimFaceSide_corner γ hγ ⟨x, hx⟩) (G.rimFaceSide_corner δ hδ ⟨x, hy⟩)

end ThomGame.Pictures.PortGraph
