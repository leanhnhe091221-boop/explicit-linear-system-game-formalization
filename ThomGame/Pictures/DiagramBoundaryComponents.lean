module

public import ThomGame.Pictures.VerticalBoundaryComponents
public import ThomGame.Pictures.DiagramBoundaryOrder

/-!
# Boundary circuits detect components of every extracted diagram

The proof uses structural induction, with no geometric or component
hypothesis on the diagram. The conclusion concerns boundary ports;
it does not identify circuit orbits with geometric disk faces.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem Diagram.graph_boundarySeesComponents (d : Diagram P u v) : d.graph.BoundarySeesComponents := by
  induction d with
  | identity w => exact PortGraph.boundarySeesComponents_identity P w
  | cap s => exact PortGraph.boundarySeesComponents_cap P s
  | cup s => exact PortGraph.boundarySeesComponents_cup P s
  | down r => exact PortGraph.boundarySeesComponents_down P r
  | up r => exact PortGraph.boundarySeesComponents_up P r
  | comp d e ihd ihe =>
    exact PortGraph.boundarySeesComponents_comp d.graph e.graph ihd ihe
      d.graph_boundaryNoncrossing e.graph_boundaryNoncrossing
  | tensor d e ihd ihe => exact PortGraph.boundarySeesComponents_tensor d.graph e.graph ihd ihe

theorem Diagram.graph_boundary_reachable_iff (d : Diagram P u v)
    (a b : PortGraph.BoundaryIndex u v) :
    d.graph.Reachable (d.graph.boundaryVertex a) (d.graph.boundaryVertex b) ↔
      d.graph.boundaryNext.SameCycle a b :=
  d.graph.boundarySeesComponents_reachable d.graph_boundarySeesComponents a b

end ThomGame.Pictures
