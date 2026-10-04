module

public import ThomGame.Pictures.GraphBoundaryCast
public import ThomGame.Pictures.CircuitCompositionFaces

/-! # Actual facial label covers under boundary reindexing -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v u' v' : List S}
  {G : PortGraph P u v} {H : PortGraph P u' v'}

theorem rotationEquiv_vertex_iff (e : G.Dart ≃ H.Dart)
    (hr : ∀ a, H.rotation (e a) = e (G.rotation a)) (a b : G.Dart) :
    (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex := by
  rw [← H.rotation_sameCycle_iff, ← G.rotation_sameCycle_iff]
  exact (FiniteReturn.sameCycle_congr G.rotation H.rotation e hr a b).symm

namespace SimpleCircuit

variable (C : G.SimpleCircuit) (hu : u = u') (hv : v = v')

@[reducible] def castBoundary : (G.cast hu hv).SimpleCircuit :=
  C.map (G.castPorts hu hv).toEmbedding
    (rotationEquiv_vertex_iff (G.castPorts hu hv) (G.castPorts_rotation hu hv))
    (G.castPorts_pairing hu hv)

theorem castBoundary_port (x : Fin C.length × Bool) :
    (C.castBoundary hu hv).port x = G.castPorts hu hv (C.port x) := C.map_port _ _ _ x

theorem castBoundary_isLabelCover (hc : C.IsLabelCover) : (C.castBoundary hu hv).IsLabelCover := by
  subst u' v'
  intro i
  exact hc i

theorem castBoundary_boundsFaceOrbit (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (C.castBoundary hu hv).BoundsFaceOrbit side := by
  subst u' v'
  exact hf

variable {w : List S} {B : PortGraph P [] w} (D : B.SimpleCircuit)

@[reducible] def bottomTopCircuit : B.bottomTopGraph.SimpleCircuit :=
  D.map (H := B.bottomTopGraph) B.bottomTopPorts.toEmbedding
    (rotationEquiv_vertex_iff (G := B) (H := B.bottomTopGraph) B.bottomTopPorts B.bottomTop_rotation)
    B.bottomTop_pairing

theorem bottomTopCircuit_port (x : Fin D.length × Bool) :
    D.bottomTopCircuit.port x = B.bottomTopPorts (D.port x) := D.map_port _ _ _ x

theorem bottomTopCircuit_isLabelCover (hc : D.IsLabelCover) : D.bottomTopCircuit.IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hi, ht, hn, hl⟩ := hc i
  refine ⟨h, k, p, q, congrArg B.bottomTopPorts hi, ?_, hn, hl⟩
  exact (B.bottomTop_pairing (D.dart i)).trans (congrArg B.bottomTopPorts ht)

theorem bottomTopCircuit_boundsFaceOrbit (side : Bool) (hf : D.BoundsFaceOrbit side) :
    D.bottomTopCircuit.BoundsFaceOrbit side :=
  D.boundsFaceOrbit_map (H := B.bottomTopGraph) B.bottomTopPorts.toEmbedding
    (rotationEquiv_vertex_iff (G := B) (H := B.bottomTopGraph) B.bottomTopPorts B.bottomTop_rotation)
    B.bottomTop_pairing
    side hf (fun _ => B.bottomTop_circuitStep _)

end SimpleCircuit
end ThomGame.Pictures.PortGraph
