module

public import ThomGame.Pictures.ConnectivitySmoothing
public import ThomGame.Pictures.DiagramBoundaryComponents

/-! # Full graph connectivity and boundary components through smoothing traces -/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

theorem smooth_boundarySeesComponents_iff (G : PortGraph P u v) (j : G.Joint) :
    (G.smooth j).BoundarySeesComponents ↔ G.BoundarySeesComponents := by
  constructor
  · intro h x y
    obtain ⟨a, rfl⟩ := G.boundaryPorts.surjective x
    obtain ⟨b, rfl⟩ := G.boundaryPorts.surjective y
    have hc := G.smooth_connected_iff j ((G.smooth j).boundaryDart a) ((G.smooth j).boundaryDart b)
    have hf := G.smooth_sameCycle_iff j ((G.smooth j).boundaryDart a) ((G.smooth j).boundaryDart b)
    rw [G.smooth_boundaryDart, G.smooth_boundaryDart] at hc hf
    exact hc.symm.trans ((h ((G.smooth j).boundaryPorts a) ((G.smooth j).boundaryPorts b)).trans hf)
  · intro h x y
    obtain ⟨a, rfl⟩ := (G.smooth j).boundaryPorts.surjective x
    obtain ⟨b, rfl⟩ := (G.smooth j).boundaryPorts.surjective y
    have hc := G.smooth_connected_iff j ((G.smooth j).boundaryDart a) ((G.smooth j).boundaryDart b)
    have hf := G.smooth_sameCycle_iff j ((G.smooth j).boundaryDart a) ((G.smooth j).boundaryDart b)
    rw [G.smooth_boundaryDart, G.smooth_boundaryDart] at hc hf
    exact hc.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf.symm)

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

theorem connected_iff (d : Smoothing G H circles) (a b : H.Dart) :
    Connected H.pairing.perm H.circuitStep a b ↔
      Connected G.pairing.perm G.circuitStep (d.portEmbedding a) (d.portEmbedding b) := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    exact (ih a b).trans (G.smooth_connected_iff j (tail.portEmbedding a) (tail.portEmbedding b))

theorem reachable_iff (d : Smoothing G H circles) (a b : H.Dart) :
    H.Reachable a.vertex b.vertex ↔ G.Reachable (d.portEmbedding a).vertex (d.portEmbedding b).vertex :=
  (H.connected_iff_vertex_reachable a b).symm.trans ((d.connected_iff a b).trans
    (G.connected_iff_vertex_reachable _ _))

theorem boundarySeesComponents_iff (d : Smoothing G H circles) :
    H.BoundarySeesComponents ↔ G.BoundarySeesComponents := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih => exact ih.trans (G.smooth_boundarySeesComponents_iff j)

theorem diagram_boundarySeesComponents {d : Diagram P u v}
    {H : PortGraph P u v} {circles : List S} (h : Smoothing d.graph H circles) :
    H.BoundarySeesComponents := h.boundarySeesComponents_iff.mpr d.graph_boundarySeesComponents

end Smoothing
end ThomGame.Pictures
