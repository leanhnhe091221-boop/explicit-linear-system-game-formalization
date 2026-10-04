module

public import ThomGame.Pictures.VerticalBoundaryOrder
public import ThomGame.Pictures.TensorBoundaryOrder
public import ThomGame.Pictures.DiagramGraph
public import ThomGame.Pictures.BoundaryOrderSmoothing

/-!
# Every actual diagram has an ordered noncrossing boundary

The five primitives and both composition operations have now been
checked for their actual extracted port graphs. Structural induction
therefore proves the condition for every diagram. Smoothing preserves
the exact boundary permutation, so it preserves this conclusion as well.
This boundary theorem does not by itself construct internal disk faces.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem Diagram.graph_boundaryNoncrossing (d : Diagram P u v) : d.graph.BoundaryNoncrossing := by
  induction d with
  | identity w => exact PortGraph.boundaryNoncrossing_identity P w
  | cap s => exact PortGraph.boundaryNoncrossing_cap P s
  | cup s => exact PortGraph.boundaryNoncrossing_cup P s
  | down r => exact PortGraph.boundaryNoncrossing_down P r
  | up r => exact PortGraph.boundaryNoncrossing_up P r
  | comp d e ihd ihe => exact PortGraph.boundaryNoncrossing_comp d.graph e.graph ihd ihe
  | tensor d e ihd ihe => exact PortGraph.boundaryNoncrossing_tensor d.graph e.graph ihd ihe

theorem Smoothing.diagram_boundaryNoncrossing {d : Diagram P u v}
    {H : PortGraph P u v} {circles : List S} (h : Smoothing d.graph H circles) :
    H.BoundaryNoncrossing := h.boundaryNoncrossing_iff.mpr d.graph_boundaryNoncrossing

end ThomGame.Pictures
