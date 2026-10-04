module

public import ThomGame.Construction.WheelDiagram
public import ThomGame.Pictures.SolutionGraph

/-! # Finite graphs extracted from diagrams over the actual numbered wheel system -/

@[expose] public section
namespace ThomGame.Construction

abbrev SigmaGraph := SolutionGroup.RowGraph numberedSystem

theorem sigmaGraph_hub_degree {u v : List (Fin 1889684)} (G : SigmaGraph u v) (h : G.Hub) :
    G.degree (.inr (.inl h)) = 3 := SolutionGroup.rowGraph_hub_degree numberedSystem G h

theorem sigmaDiagram_graph_sign {u v : List (Fin 1889684)} (d : SigmaDiagram u v) :
    d.graph.sign = d.character (rowEquiv oddRow) :=
  d.graph_sign.trans (sigmaDiagram_sign d)

theorem sigmaDiagram_graph_hub_card {u v : List (Fin 1889684)} (d : SigmaDiagram u v) :
    Fintype.card d.graph.Hub = d.size := d.graph_hub_card

theorem J_sigma_eq_one_iff_closed_minimal_odd_extracted_graph :
    J_sigma = 1 ↔ ∃ d : SigmaDiagram [] [], d.graph.sign = 1 ∧ d.Minimal := by
  simp only [Pictures.Diagram.graph_sign]
  exact J_sigma_eq_one_iff_closed_minimal_odd_diagram

end ThomGame.Construction
