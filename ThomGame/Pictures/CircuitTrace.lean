module

public import ThomGame.Pictures.CircuitCounts

/-!
# Circuits along a complete smoothing trace

The retained circuit map is injective, reflects the same-circuit relation,
and has exactly two missing circuits per recorded isolated circle.
The Euler expression here is only a finite combinatorial count; it is not
asserted to be the Euler characteristic of an established planar embedding.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

variable (G : PortGraph P u v)

theorem vertex_card : Fintype.card G.Vertex =
    (u.length + v.length) + (Fintype.card G.Hub + Fintype.card G.Joint) := by
  change Fintype.card ((Fin u.length ⊕ Fin v.length) ⊕ (G.Hub ⊕ G.Joint)) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

theorem smooth_vertex_card (j : G.Joint) :
    Fintype.card (G.smooth j).Vertex + 1 = Fintype.card G.Vertex := by
  rw [G.vertex_card, (G.smooth j).vertex_card, G.smooth_hub_card]
  have h := G.smooth_joint_card j
  omega

/-- The integer expression V - E + C, with C the permutation-circuit count. -/
noncomputable def ribbonEuler : Int :=
  (Fintype.card G.Vertex : Int) - Fintype.card G.Edge + Fintype.card G.Circuit

theorem smooth_ribbonEuler (j : G.Joint) :
    G.ribbonEuler = (G.smooth j).ribbonEuler + 2 * (G.smoothCircles j).length := by
  have hv := G.smooth_vertex_card j
  have he := G.smooth_edge_card j
  have hc := G.smooth_circuit_card j
  unfold ribbonEuler
  omega

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

noncomputable def circuitEmbedding : {G H : PortGraph P u v} → {circles : List S} →
    Smoothing G H circles → H.Circuit ↪ G.Circuit
  | _, _, _, .refl _ => Function.Embedding.refl _
  | G, _, _, .step j tail => tail.circuitEmbedding.trans (G.smoothCircuitEmbedding j)

theorem circuitEmbedding_circuit (d : Smoothing G H circles) (a : H.Dart) :
    d.circuitEmbedding (H.circuit a) = G.circuit (d.portEmbedding a) := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    change G.smoothCircuitMap j (tail.circuitEmbedding (H.circuit a)) = _
    rw [ih, G.smoothCircuitMap_circuit]
    rfl

theorem sameCircuit_iff (d : Smoothing G H circles) (a b : H.Dart) :
    H.circuit a = H.circuit b ↔ G.circuit (d.portEmbedding a) = G.circuit (d.portEmbedding b) := by
  rw [← d.circuitEmbedding_circuit, ← d.circuitEmbedding_circuit]
  exact d.circuitEmbedding.injective.eq_iff.symm

theorem circuit_card (d : Smoothing G H circles) :
    Fintype.card H.Circuit + 2 * circles.length = Fintype.card G.Circuit := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    have h := G.smooth_circuit_card j
    rw [List.length_append]
    omega

theorem vertex_card (d : Smoothing G H circles) :
    Fintype.card H.Vertex + d.steps = Fintype.card G.Vertex := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    have h := G.smooth_vertex_card j
    change Fintype.card H.Vertex + (tail.steps + 1) = _
    omega

theorem ribbonEuler (d : Smoothing G H circles) :
    G.ribbonEuler = H.ribbonEuler + 2 * circles.length := by
  have hv := d.vertex_card
  have he := d.edge_card
  have hc := d.circuit_card
  unfold PortGraph.ribbonEuler
  omega

end Smoothing
end ThomGame.Pictures
