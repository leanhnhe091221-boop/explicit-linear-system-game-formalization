module

public import ThomGame.Pictures.DiagramGraph
public import ThomGame.Pictures.GraphEdges
public import ThomGame.Pictures.SolutionDiagram

/-! # The extracted graphs for actual three-variable solution-group relations -/

@[expose] public section
namespace ThomGame.SolutionGroup

open Pictures

variable {R C : Type*} (S : SparseSystem R C) {u v : List C}

abbrev RowGraph := PortGraph (triangularPresentation S)

theorem rowGraph_hub_degree (G : RowGraph S u v) (h : G.Hub) :
    G.degree (.inr (.inl h)) = 3 := G.degree_hub h

theorem rowGraph_port_label (G : RowGraph S u v) (h : G.Hub) (i : Fin 3) :
    Port.label G.jointLabel (.hub h i : G.Dart) = S.column (G.hubLabel h) i := by
  fin_cases i <;> rfl

theorem rowGraph_not_adj_self_hub (G : RowGraph S u v) (h : G.Hub) :
    ¬ G.Adj (.inr (.inl h)) (.inr (.inl h)) := by
  apply G.not_adj_self_hub h
  intro i j hij
  apply S.column_injective (G.hubLabel h)
  change Port.label G.jointLabel (.hub h i : G.Dart) =
    Port.label G.jointLabel (.hub h j : G.Dart) at hij
  exact (rowGraph_port_label S G h i).symm.trans (hij.trans (rowGraph_port_label S G h j))

theorem rowGraph_degree_sum (G : RowGraph S u v) :
    u.length + v.length + (3 * Fintype.card G.Hub + 2 * Fintype.card G.Joint) =
      2 * Fintype.card G.Edge := by
  have h := G.degree_sum
  change u.length + v.length + ((∑ _ : G.Hub, 3) + 2 * Fintype.card G.Joint) = _ at h
  simpa [mul_comm] using h

theorem rowDiagram_graph_sign (d : RowDiagram S u v) : d.graph.sign = d.sign := d.graph_sign

/-- Existence includes the originating diagram; an arbitrary finite row graph
is not asserted to have a valid planar realization. -/
theorem word_eq_iff_extracted_graph (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ d : RowDiagram S w [], d.graph.sign = a := by
  simp only [Diagram.graph_sign]
  exact word_eq_iff_diagram S w a

end ThomGame.SolutionGroup
