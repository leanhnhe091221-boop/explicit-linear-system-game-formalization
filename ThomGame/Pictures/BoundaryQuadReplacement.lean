module

public import ThomGame.Pictures.BoundaryQuadPath
public import ThomGame.Pictures.CircuitLocalEmbedding

/-!
# An exact interface for replacing a graph while retaining its outer quadrilaterals

Boundary positions are fixed. Each original quadrilateral retains its
specified three ports, both endpoints of its edges and their labels.
The interface makes no assertion about pairings elsewhere in the graph.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  (G H : PortGraph P u v)

structure BoundaryQuadReplacement where
  ports : G.Dart ≃ H.Dart
  boundary : ∀ i, ports (G.boundaryDart i) = H.boundaryDart i
  vertices : ∀ a b, (ports a).vertex = (ports b).vertex ↔ a.vertex = b.vertex
  quadPath : G.BoundaryQuadPath → H.BoundaryQuadPath
  first : ∀ p, (quadPath p).firstDart = ports p.firstDart
  middle : ∀ p, (quadPath p).middleDart = ports p.middleDart
  last : ∀ p, (quadPath p).lastDart = ports p.lastDart
  pairs : ∀ p : G.BoundaryQuadPath, ∀ x ∈ [p.firstDart, p.middleDart, p.lastDart],
    H.pairing.twin (ports x) = ports (G.pairing.twin x)
  labels : ∀ p : G.BoundaryQuadPath, ∀ x ∈ [p.firstDart, p.middleDart, p.lastDart],
    Port.label H.jointLabel (ports x) = Port.label G.jointLabel x

namespace BoundaryQuadReplacement

variable {G H} (r : G.BoundaryQuadReplacement H) (p : G.BoundaryQuadPath)

theorem start : (r.quadPath p).start = p.start :=
  H.boundaryDart.injective ((r.first p).trans (r.boundary p.start))

theorem finish : (r.quadPath p).finish = p.finish := by
  apply H.boundaryDart.injective
  rw [← (r.quadPath p).last_twin, r.last, r.pairs p p.lastDart (by simp), p.last_twin]
  exact r.boundary p.finish

theorem circuitStep : ∀ x ∈ [p.firstDart, p.middleDart, p.lastDart],
    H.circuitStep (r.ports x) = r.ports (G.circuitStep x) := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [← r.first, (r.quadPath p).first_step, p.first_step]
    exact r.middle p
  · rw [← r.middle, (r.quadPath p).second_step, p.second_step]
    exact r.last p
  · rw [← r.last, (r.quadPath p).last_step, p.last_step, r.finish]
    exact (r.boundary p.finish).symm

theorem labels_twin : ∀ x ∈ [p.firstDart, p.middleDart, p.lastDart],
    Port.label H.jointLabel (r.ports (G.pairing.twin x)) = Port.label G.jointLabel (G.pairing.twin x) := by
  intro x hx
  rw [← r.pairs p x hx, H.pairing.label_twin, G.pairing.label_twin]
  exact r.labels p x hx

end BoundaryQuadReplacement
end ThomGame.Pictures.PortGraph
