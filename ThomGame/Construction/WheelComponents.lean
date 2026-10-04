module

public import ThomGame.Construction.WheelGraph
public import ThomGame.Pictures.GraphComponentCounts
public import ThomGame.Pictures.DiagramEuler
public import ThomGame.Pictures.ComponentSmoothingTrace
public import ThomGame.Pictures.SmoothingEuler
public import ThomGame.Pictures.ReducedComponents

/-!
# Actual component quotients and Euler counts for the numbered system

Every row hub has three ports, so the no-empty-hub hypotheses of the
generic quotient correspondences are discharged for every actual row
graph. Extracted diagrams also satisfy the proved zero-defect identity.
This does not construct a planar embedding or disk faces.
-/

@[expose] public section
namespace ThomGame.Construction

variable {u v : List (Fin 1889684)}

theorem sigmaGraph_component_card (G : SigmaGraph u v) :
    Nat.card (Pictures.RibbonConnectivity.Component G.pairing.perm G.circuitStep) =
      Nat.card G.GraphComponent :=
  Nat.card_congr (G.dartComponentEquiv (fun _ => by change 0 < 3; omega))

theorem sigmaGraph_eulerCount (G : SigmaGraph u v) :
    Pictures.RibbonConnectivity.eulerCount G.pairing.perm G.circuitStep = G.ribbonEuler :=
  G.eulerCount_eq_ribbonEuler (fun _ => by change 0 < 3; omega)

theorem sigmaGraph_eulerDefect (G : SigmaGraph u v) :
    Pictures.RibbonConnectivity.eulerDefect G.pairing.perm G.circuitStep =
      G.ribbonEuler - 2 * Nat.card G.GraphComponent :=
  G.eulerDefect_eq_ribbonEuler (fun _ => by change 0 < 3; omega)

theorem sigmaDiagram_boundarySeesComponents (d : SigmaDiagram u v) :
    d.graph.BoundarySeesComponents := d.graph_boundarySeesComponents

theorem sigmaDiagram_eulerDefect (d : SigmaDiagram u v) :
    Pictures.RibbonConnectivity.eulerDefect d.graph.pairing.perm d.graph.circuitStep = 0 :=
  d.graph_eulerDefect

theorem sigmaDiagram_ribbonEuler (d : SigmaDiagram u v) :
    d.graph.ribbonEuler = 2 * (Nat.card d.graph.GraphComponent : Int) :=
  d.graph_ribbonEuler (fun _ => by change 0 < 3; omega)

theorem smoothed_sigma_boundarySeesComponents {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.BoundarySeesComponents := h.diagram_boundarySeesComponents

theorem smoothed_sigma_graphComponent_card {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    Nat.card H.GraphComponent + circles.length = Nat.card d.graph.GraphComponent :=
  h.graphComponent_card (fun _ => by change 0 < 3; omega)

theorem smoothed_sigma_eulerDefect {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    Pictures.RibbonConnectivity.eulerDefect H.pairing.perm H.circuitStep = 0 :=
  h.diagram_eulerDefect (fun _ => by change 0 < 3; omega)

theorem smoothed_sigma_ribbonEuler_eq_components {d : SigmaDiagram u v}
    {H : SigmaGraph u v} {circles : List (Fin 1889684)} (h : Pictures.Smoothing d.graph H circles) :
    H.ribbonEuler = 2 * (Nat.card H.GraphComponent : Int) :=
  h.diagram_ribbonEuler (fun _ => by change 0 < 3; omega)

end ThomGame.Construction
