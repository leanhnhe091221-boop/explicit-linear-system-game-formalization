module

public import ThomGame.Construction.WheelGraph
public import ThomGame.Pictures.SolutionSmoothing
public import ThomGame.Pictures.ReducedCircuits
public import ThomGame.Pictures.BoundaryOrderSmoothing
public import ThomGame.Pictures.DiagramBoundaryOrder

/-! # Junction elimination for the actual numbered wheel system -/

@[expose] public section
namespace ThomGame.Construction

theorem smoothed_sigma_sign {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.sign = d.character (rowEquiv oddRow) := h.sign.trans (sigmaDiagram_graph_sign d)

theorem smoothed_sigma_hub_card {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    Fintype.card H.Hub = d.size := h.hub_card.trans d.graph_hub_card

theorem smoothed_sigma_circuit_card {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    Fintype.card H.Circuit + 2 * circles.length = Fintype.card d.graph.Circuit := h.circuit_card

theorem smoothed_sigma_ribbonEuler {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    d.graph.ribbonEuler = H.ribbonEuler + 2 * circles.length := h.ribbonEuler

theorem smoothed_sigma_circuit_range {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles)
    [IsEmpty H.Joint] (c : d.graph.Circuit) :
    (∃ q : H.Circuit, h.circuitEmbedding q = c) ↔ d.graph.CircuitHasTerminal c :=
  h.circuitEmbedding_range_iff c

theorem smoothed_sigma_boundaryNext {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.boundaryNext = d.graph.boundaryNext := h.boundaryNext

theorem smoothed_sigma_boundaryNoncrossing_iff {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.BoundaryNoncrossing ↔ d.graph.BoundaryNoncrossing := h.boundaryNoncrossing_iff

theorem sigmaDiagram_boundaryNoncrossing {u v : List (Fin 1889684)} (d : SigmaDiagram u v) :
    d.graph.BoundaryNoncrossing := d.graph_boundaryNoncrossing

theorem smoothed_sigma_boundaryNoncrossing {u v : List (Fin 1889684)} {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.BoundaryNoncrossing := h.diagram_boundaryNoncrossing

theorem J_sigma_eq_one_iff_closed_minimal_smoothed_graph :
    J_sigma = 1 ↔
      ∃ (d : SigmaDiagram [] []) (H : SigmaGraph [] []) (circles : List (Fin 1889684)),
        d.Minimal ∧ Nonempty (Pictures.Smoothing d.graph H circles) ∧ IsEmpty H.Joint ∧ H.sign = 1 :=
  SolutionGroup.J_eq_one_iff_closed_minimal_smoothed_graph numberedSystem

end ThomGame.Construction
