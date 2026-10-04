module

public import ThomGame.Pictures.CircuitLabelCopies
public import ThomGame.Pictures.RimNonfacialCount

/-! # Equal-labelled marked ports of a genuine copy belong to one actual edge -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} {A : SparseSystem R S} {G : SolutionGroup.RowGraph A [] []}

namespace SimpleCircuit

variable (C : G.SimpleCircuit)

theorem marked_edge_label {x : G.Dart} (hx : C.Marked x) :
    ∃ i : Fin C.length, G.pairing.edge x = G.pairing.edge (C.dart i) ∧
      Port.label G.jointLabel x = Port.label G.jointLabel (C.dart i) := by
  obtain ⟨⟨i, side⟩, rfl⟩ := hx
  cases side
  · exact ⟨i, rfl, rfl⟩
  · exact ⟨(finRotate C.length).symm i, G.pairing.edge_twin _, G.pairing.label_twin _⟩

theorem copy_edge_eq_of_marked_label (hc : C.IsLabelCopy) {x y : G.Dart}
    (hx : C.Marked x) (hy : C.Marked y)
    (hl : Port.label G.jointLabel x = Port.label G.jointLabel y) :
    G.pairing.edge x = G.pairing.edge y := by
  obtain ⟨i, hi, hil⟩ := C.marked_edge_label hx
  obtain ⟨j, hj, hjl⟩ := C.marked_edge_label hy
  have he := hc.2 (hil.symm.trans (hl.trans hjl))
  exact hi.trans ((congrArg (fun k => G.pairing.edge (C.dart k)) he).trans hj.symm)

end SimpleCircuit

variable [DecidableEq R] [DecidableEq S] (γ : Hypergraph.Cycle A.hypergraph)

theorem rim_components_ne_of_copies
    (hc : ∀ a : G.RimDart γ, (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).IsLabelCopy)
    (x y : G.RimDart γ) (he : G.pairing.edge x.val ≠ G.pairing.edge y.val)
    (hl : Port.label G.jointLabel x.val = Port.label G.jointLabel y.val) :
    G.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x ≠ G.rimComponent γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim y := by
  intro hxy
  let C := G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x
  exact he (C.copy_edge_eq_of_marked_label (hc x)
    (G.rimSimpleCircuit_marked_of_component γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x x rfl)
    (G.rimSimpleCircuit_marked_of_component γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x y hxy) hl)

end ThomGame.Pictures.PortGraph
