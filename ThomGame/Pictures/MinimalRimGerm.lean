module

public import ThomGame.Pictures.MinimalSmoothedGerm
public import ThomGame.Pictures.CycleGermCharge

/-! # Stellar rims in minimal odd row diagrams -/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}

/-- The unconditional germ conclusion, with the actual graph and boundary. -/
def PortGraph.RimHasZeroSignGerm (G : SolutionGroup.RowGraph A [] [])
    (C : Hypergraph.Cycle A.hypergraph)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))
    (a : G.RimDart C) : Prop :=
  ∃ s, ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).sign = 0

theorem Diagram.minimal_odd_stellar_rim_hasZeroSignGerm
    (d : SolutionGroup.RowDiagram A [] []) (hmin : d.Minimal) (hs : d.sign = 1)
    (C : Hypergraph.Cycle A.hypergraph) (a : d.graph.RimDart C) (hc : C.Stellar A.rhs) :
    d.graph.RimHasZeroSignGerm C d.graph_dualEuler a :=
  d.minimal_odd_circuit_exists_germ_sign_zero hmin hs
    (d.graph.rimSimpleCircuit C (by simp) (by simp) a)
    (d.graph.rimSimpleCircuit_stellar_sign C a hc)

theorem Smoothing.minimal_odd_stellar_rim_hasZeroSignGerm
    {d : SolutionGroup.RowDiagram A [] []} {H : SolutionGroup.RowGraph A [] []} {circles : List S}
    (t : Smoothing d.graph H circles) (hmin : d.Minimal) (hs : d.sign = 1)
    (C : Hypergraph.Cycle A.hypergraph) (a : H.RimDart C) (hc : C.Stellar A.rhs) :
    H.RimHasZeroSignGerm C (t.diagram_dualEuler (fun _ => by change 0 < 3; omega)) a :=
  t.minimal_odd_circuit_exists_germ_sign_zero hmin hs
    (fun _ => by change 0 < 3; omega) (H.rimSimpleCircuit C (by simp) (by simp) a)
    (H.rimSimpleCircuit_stellar_sign C a hc)

end ThomGame.Pictures
