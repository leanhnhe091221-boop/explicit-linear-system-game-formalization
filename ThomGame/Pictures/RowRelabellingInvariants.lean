module

public import ThomGame.Pictures.RowGraphRelabelling
public import ThomGame.Pictures.RowGraphEmbeddingInvariants
public import ThomGame.Pictures.BoundaryQuadCapping

/-! # Actual boundaries, Euler data and outer quadrilaterals under row relabelling -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowRelabelling

open Equiv RibbonConnectivity

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} {G : SolutionGroup.RowGraph A u v} (m : G.RowRelabelling B)

theorem ports_vertex_iff (a b : G.Dart) :
    (m.ports a).vertex = (m.ports b).vertex ↔ a.vertex = b.vertex :=
  (m.graph.rotation_sameCycle_iff _ _).symm.trans
    ((FiniteReturn.sameCycle_congr _ _ m.ports m.ports_rotation a b).symm.trans
      (G.rotation_sameCycle_iff a b))

theorem ports_boundary_iff (a : G.Dart) : m.graph.IsBoundary (m.ports a) ↔ G.IsBoundary a := by
  cases a <;> rfl

theorem ports_boundaryDart (i : BoundaryIndex u v) :
    m.ports (G.boundaryDart i) = m.graph.boundaryDart (mapBoundaryIndex m.edge u v i) := by
  cases i <;> rfl

theorem boundaryNext (i : BoundaryIndex u v) :
    m.graph.boundaryNext (mapBoundaryIndex m.edge u v i) =
      mapBoundaryIndex m.edge u v (G.boundaryNext i) := by
  have hr := MarkedReturn.perm_preserved_of_commutes m.graph.circuitStep m.graph.IsBoundary
    G.circuitStep G.IsBoundary m.ports m.ports_circuitStep m.ports_boundary_iff (G.boundaryPorts i)
  have he : (⟨m.ports (G.boundaryPorts i).val,
      (m.ports_boundary_iff _).mpr (G.boundaryPorts i).property⟩ : Subtype m.graph.IsBoundary) =
        m.graph.boundaryPorts (mapBoundaryIndex m.edge u v i) := by cases i <;> rfl
  rw [he, G.boundaryPorts_next, m.graph.boundaryPorts_next] at hr
  apply m.graph.boundaryDart.injective
  exact hr.symm.trans (m.ports_boundaryDart _)

theorem noncrossing (h : G.BoundaryNoncrossing) : m.graph.BoundaryNoncrossing :=
  h.transport (mapBoundaryIndex m.edge u v) (mapBoundaryIndex_cyclic m.edge u v)
    m.boundaryNext (mapBoundaryIndex_between m.edge u v)

theorem sees (h : G.BoundarySeesComponents) : m.graph.BoundarySeesComponents := by
  intro x y
  obtain ⟨a, ha⟩ := m.graph.boundaryPorts.surjective x
  obtain ⟨a, rfl⟩ := (mapBoundaryIndex m.edge u v).surjective a
  obtain ⟨b, hb⟩ := m.graph.boundaryPorts.surjective y
  obtain ⟨b, rfl⟩ := (mapBoundaryIndex m.edge u v).surjective b
  rw [← ha, ← hb]
  have hc := connected_congr G.pairing.perm G.circuitStep m.graph.pairing.perm
    m.graph.circuitStep m.ports m.ports_twin m.ports_circuitStep (G.boundaryDart a) (G.boundaryDart b)
  have hf := FiniteReturn.sameCycle_congr _ _ m.ports m.ports_circuitStep (G.boundaryDart a) (G.boundaryDart b)
  rw [m.ports_boundaryDart, m.ports_boundaryDart] at hc hf
  exact hc.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf)

theorem eulerDefect : RibbonConnectivity.eulerDefect m.graph.pairing.perm m.graph.circuitStep =
    RibbonConnectivity.eulerDefect G.pairing.perm G.circuitStep :=
  (eulerDefect_congr _ _ _ _ m.ports m.ports_twin m.ports_circuitStep).symm

theorem connected_iff (a b : G.Dart) :
    Connected m.graph.rotation m.graph.pairing.perm (m.ports a) (m.ports b) ↔
      Connected G.rotation G.pairing.perm a b :=
  (connected_congr _ _ _ _ m.ports m.ports_rotation m.ports_twin a b).symm

noncomputable def quadPath (q : G.BoundaryQuadPath) : m.graph.BoundaryQuadPath where
  start := mapBoundaryIndex m.edge u v q.start
  finish := mapBoundaryIndex m.edge u v q.finish
  firstHub := q.firstHub
  secondHub := q.secondHub
  firstSlot := m.slotEquiv q.firstHub q.firstSlot
  secondSlot := m.slotEquiv q.secondHub q.secondSlot
  first_step := by
    rw [← m.ports_boundaryDart, m.ports_circuitStep, q.first_step]
    rfl
  second_step := by
    change m.graph.circuitStep (m.ports q.middleDart) = _
    rw [m.ports_circuitStep, q.second_step]
    rfl
  last_step := by
    change m.graph.circuitStep (m.ports q.lastDart) = _
    rw [m.ports_circuitStep, q.last_step, m.ports_boundaryDart]
  boundary_adjacent := (mapBoundaryIndex_cyclic m.edge u v q.start).trans
    (congrArg (mapBoundaryIndex m.edge u v) q.boundary_adjacent)
  ends_distinct := fun he => q.ends_distinct ((mapBoundaryIndex m.edge u v).injective he)
  hubs_distinct := q.hubs_distinct

theorem quadPath_firstDart (q : G.BoundaryQuadPath) :
    (m.quadPath q).firstDart = m.ports q.firstDart := (m.ports_boundaryDart q.start).symm

theorem quadPath_middleDart (q : G.BoundaryQuadPath) : (m.quadPath q).middleDart = m.ports q.middleDart := rfl

theorem quadPath_lastDart (q : G.BoundaryQuadPath) : (m.quadPath q).lastDart = m.ports q.lastDart := rfl

theorem quadPath_capped_face (q : G.BoundaryQuadPath) (x : m.graph.Dart) :
    (m.graph.cappedRotation * m.graph.pairing.perm).SameCycle (m.ports q.firstDart) x ↔
      x = m.ports q.firstDart ∨ x = m.ports q.middleDart ∨ x = m.ports q.lastDart := by
  simpa only [m.quadPath_firstDart, m.quadPath_middleDart, m.quadPath_lastDart] using
    (m.quadPath q).capped_face_iff x

end ThomGame.Pictures.PortGraph.RowRelabelling
