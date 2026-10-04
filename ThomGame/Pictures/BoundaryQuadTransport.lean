module

public import ThomGame.Pictures.GraphBoundaryCast
public import ThomGame.Pictures.BoundaryQuadPath

/-! # Transporting exact quadrilaterals to the top and along boundary equality -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.BoundaryQuadPath

variable {R S : Type*} {P : InvolutionPresentation R S}
  {u v u' v' w : List S}

def castBoundary {G : PortGraph P u v} (q : G.BoundaryQuadPath) (hu : u = u') (hv : v = v') :
    (G.cast hu hv).BoundaryQuadPath := by
  subst u' v'
  exact q

theorem castBoundary_firstDart {G : PortGraph P u v} (q : G.BoundaryQuadPath)
    (hu : u = u') (hv : v = v') : (q.castBoundary hu hv).firstDart = G.castPorts hu hv q.firstDart := by
  subst u' v'
  rfl

theorem castBoundary_middleDart {G : PortGraph P u v} (q : G.BoundaryQuadPath)
    (hu : u = u') (hv : v = v') : (q.castBoundary hu hv).middleDart = G.castPorts hu hv q.middleDart := by
  subst u' v'
  rfl

theorem castBoundary_lastDart {G : PortGraph P u v} (q : G.BoundaryQuadPath)
    (hu : u = u') (hv : v = v') : (q.castBoundary hu hv).lastDart = G.castPorts hu hv q.lastDart := by
  subst u' v'
  rfl

variable {G : PortGraph P [] w} (q : G.BoundaryQuadPath)

def bottomTop : G.bottomTopGraph.BoundaryQuadPath where
  start := bottomTopIndex w q.start
  finish := bottomTopIndex w q.finish
  firstHub := q.firstHub
  secondHub := q.secondHub
  firstSlot := q.firstSlot
  secondSlot := q.secondSlot
  first_step := by
    rw [← G.bottomTop_boundaryDart, G.bottomTop_circuitStep, q.first_step]
    rfl
  second_step := (G.bottomTop_circuitStep q.middleDart).trans (congrArg G.bottomTopPorts q.second_step)
  last_step := (G.bottomTop_circuitStep q.lastDart).trans
    ((congrArg G.bottomTopPorts q.last_step).trans (G.bottomTop_boundaryDart q.finish))
  boundary_adjacent := (bottomTopIndex_cyclic w q.start).trans (congrArg (bottomTopIndex w) q.boundary_adjacent)
  ends_distinct := fun he => q.ends_distinct ((bottomTopIndex w).injective he)
  hubs_distinct := q.hubs_distinct

theorem bottomTop_firstDart : q.bottomTop.firstDart = G.bottomTopPorts q.firstDart :=
  (G.bottomTop_boundaryDart q.start).symm

theorem bottomTop_middleDart : q.bottomTop.middleDart = G.bottomTopPorts q.middleDart := rfl

theorem bottomTop_lastDart : q.bottomTop.lastDart = G.bottomTopPorts q.lastDart := rfl

end ThomGame.Pictures.PortGraph.BoundaryQuadPath
