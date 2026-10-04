module

public import ThomGame.Construction.WheelConstellation
public import ThomGame.Construction.WheelGraph
public import ThomGame.Pictures.CycleSimpleCircuit

/-!
# Restricted rim graphs in the actual numbered solution graph

Every central cycle and pentagon restricts every closed numbered row
graph to the proved two-regular finite incidence data. This includes
graphs extracted from diagrams and all of their smoothed versions.
No planarity or disk-region theorem is inferred from the restriction.
-/

@[expose] public section
namespace ThomGame.Construction

def numberedWheelCycles : WheelCycleIndex → Hypergraph.Cycle numberedSystem.hypergraph
  | .inl r => numberedCentralWheelCycle r
  | .inr ⟨r, j⟩ => numberedPentagonWheelCycle r j

theorem closed_sigma_rimIncident_card (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) :
    Fintype.card (G.RimIncident (numberedWheelCycles i) a.val.vertex) = 2 :=
  G.rimIncident_card _ (by simp) (by simp) a

noncomputable def closedSigmaRimWalk (G : SigmaGraph [] []) (i : WheelCycleIndex) :
    Equiv.Perm (G.RimDart (numberedWheelCycles i)) :=
  G.rimWalk _ (by simp) (by simp)

theorem closedSigmaRimWalk_vertex (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) :
    (closedSigmaRimWalk G i a).val.vertex = (G.pairing.twin a.val).vertex :=
  G.rimWalk_vertex _ (by simp) (by simp) a

def ClosedSigmaRimComponent (G : SigmaGraph [] []) (i : WheelCycleIndex) :=
  G.RimComponent (numberedWheelCycles i) (by simp) (by simp)

noncomputable instance (G : SigmaGraph [] []) (i : WheelCycleIndex) :
    Fintype (ClosedSigmaRimComponent G i) := by
  unfold ClosedSigmaRimComponent
  infer_instance

noncomputable def closedSigmaRimCircuit (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a : G.RimDart (numberedWheelCycles i)) : G.SimpleCircuit :=
  G.rimSimpleCircuit _ (by simp) (by simp) a

theorem closedSigmaRimCircuit_vertex_complete (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a b : G.RimDart (numberedWheelCycles i))
    (hab : G.rimComponent (numberedWheelCycles i) (by simp) (by simp) a =
      G.rimComponent (numberedWheelCycles i) (by simp) (by simp) b) :
    ∃! j : Fin (closedSigmaRimCircuit G i a).length,
      ((closedSigmaRimCircuit G i a).dart j).vertex = b.val.vertex :=
  G.rimSimpleCircuit_vertex_complete _ (by simp) (by simp) a b hab

theorem closedSigmaRimCircuit_edge_complete (G : SigmaGraph [] []) (i : WheelCycleIndex)
    (a b : G.RimDart (numberedWheelCycles i))
    (hab : G.rimComponent (numberedWheelCycles i) (by simp) (by simp) a =
      G.rimComponent (numberedWheelCycles i) (by simp) (by simp) b) :
    ∃! j : Fin (closedSigmaRimCircuit G i a).length,
      G.pairing.edge ((closedSigmaRimCircuit G i a).dart j) = G.pairing.edge b.val :=
  G.rimSimpleCircuit_edge_complete _ (by simp) (by simp) a b hab

end ThomGame.Construction
