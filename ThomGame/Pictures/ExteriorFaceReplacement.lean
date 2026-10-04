module

public import ThomGame.Pictures.LiftedFaceReplacement

/-!
# Original faces disjoint from the germ survive replacement

Disjointness is stated on the actual original vertices. A germ-side
port projects either to a germ vertex or to a face port whose successor
has a germ vertex. Thus a face disjoint from the germ has no germ-side
ports in its lift. The local quadrilateral condition follows vacuously,
and the final smoothed face has exactly the original ports and labels.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

theorem germFaceSource_meets_germ (x : (C.germGraph hEuler s).swapBoundary.Dart) :
    C.GermVertex s (C.germFaceSource hEuler s x).vertex ∨
      C.GermVertex s (G.circuitStep (C.germFaceSource hEuler s x)).vertex := by
  cases x with
  | top i =>
    right
    change C.GermVertex s (G.circuitStep (G.pairing.twin (C.boundaryEnumeration (!s) i).val)).vertex
    rw [G.vertex_circuitStep, G.pairing.involutive]
    exact Or.inl ((C.frontier_iff hEuler (!s) _).mp (C.boundaryEnumeration (!s) i).property).1
  | bottom i => exact i.elim0
  | hub h i => exact Or.inl h.property
  | joint j b => exact Or.inl j.property

variable (hc : ∀ x y : G.Vertex, G.Reachable x y)
  (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)
  (hout : ∀ k : Fin D.length, ¬ C.GermVertex s (D.port (k, side)).vertex)

include hf hout in
theorem exteriorFace_not_germ_source (x : (C.germGraph hEuler s).swapBoundary.Dart) :
    ¬ G.circuitStep.SameCycle (C.germFaceSource hEuler s x) (D.port (0, side)) := by
  intro hx
  rcases C.germFaceSource_meets_germ hEuler s x with hv | hv
  · obtain ⟨k, hk⟩ := (hf _).mp hx
    exact hout k (hk.symm ▸ hv)
  · obtain ⟨k, hk⟩ := (hf _).mp hx.apply_left
    exact hout k (hk.symm ▸ hv)

include hf hout in
theorem exteriorLiftedCircuit_avoids_germ
    (k : Fin (C.orientedLiftedCircuit hEuler hc s D side hf).length)
    (x : (C.germGraph hEuler s).swapBoundary.Dart) :
    (C.orientedLiftedCircuit hEuler hc s D side hf).port (k, false) ≠
      compRightEmbedding (C.regionGraph hEuler (!s)).swapBoundary
        (C.germGraph hEuler s).swapBoundary x := by
  intro he
  have hx := C.orientedLiftedCircuit_source hEuler hc s D side hf k
  change G.circuitStep.SameCycle
    (C.orientedFaceProjection hEuler s ((C.orientedLiftedCircuit hEuler hc s D side hf).port (k, false)))
    (D.port (0, side)) at hx
  rw [he, C.orientedFaceProjection_germ] at hx
  exact C.exteriorFace_not_germ_source hEuler s D side hf hout x hx

include hf hout in
theorem exteriorLiftedCircuit_supported :
    (C.orientedLiftedCircuit hEuler hc s D side hf).SupportedByQuads false := by
  intro k x he
  exact (C.exteriorLiftedCircuit_avoids_germ hEuler s hc D side hf hout k x he).elim

variable [IsEmpty G.Joint] {N : PortGraph P (C.frontierWord (!s)) []} [IsEmpty N.Joint]
  (r : (C.germGraph hEuler s).swapBoundary.BoundaryQuadReplacement N)
  (red : ClosedGluingReduction (C.regionGraph hEuler (!s)).swapBoundary N)

include hf hout in
theorem exteriorFace_replacement_survives :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧ F.length = D.length ∧
      ∃ e : Fin F.length ≃ Fin D.length, ∀ j : Fin F.length,
        red.trace.portEmbedding (F.dart j) =
          r.gluedPorts (C.regionGraph hEuler (!s)).swapBoundary
            (C.orientedLiftPort hEuler hc s (D.port (e j, side))) ∧
        Port.label red.graph.jointLabel (F.dart j) = Port.label G.jointLabel (D.port (e j, side)) :=
  C.liftedFace_replacement_survives_equiv hEuler hc s D side hf
    (C.exteriorLiftedCircuit_supported hEuler s hc D side hf hout) r red

end ThomGame.Pictures.PortGraph.SimpleCircuit
