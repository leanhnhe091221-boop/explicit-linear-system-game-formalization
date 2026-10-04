module

public import ThomGame.Pictures.QuadReplacementGluing

/-!
# Whole facial circuits survive replacement along outer quadrilaterals

A circuit may alternate arbitrarily often between the complementary
graph and the replaced graph. When each of its face darts on the latter
side belongs to an outer quadrilateral, the actual glued port map
transports its complete simple circuit and exact face orbit. Establishing
this local support condition from cycle intersection hypotheses is a
separate step.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {v : List S}
  {E : PortGraph P [] v} {G H : PortGraph P v []}

def SimpleCircuit.SupportedByQuads (C : (E.comp G).SimpleCircuit) (side : Bool) : Prop :=
  ∀ i x, C.port (i, side) = compRightEmbedding E G x →
    ∃ p : G.BoundaryQuadPath, x ∈ [p.firstDart, p.middleDart, p.lastDart]

namespace BoundaryQuadReplacement

variable (r : G.BoundaryQuadReplacement H) (C : (E.comp G).SimpleCircuit)
  (side : Bool) (h : C.SupportedByQuads side)

include h in
theorem supported_face_pair (i : Fin C.length) :
    (E.comp H).pairing.twin (r.gluedPorts E (C.port (i, side))) =
      r.gluedPorts E ((E.comp G).pairing.twin (C.port (i, side))) := by
  obtain ⟨x, hx⟩ := (compPorts E G).surjective (C.port (i, side))
  rcases x with x | x
  · rw [← hx]
    exact r.gluedPorts_left_pair E x
  · obtain ⟨p, hp⟩ := h i x hx.symm
    rw [← hx]
    exact r.gluedPorts_right_pair E x (r.pairs p x hp)

include h in
theorem supported_face_step (i : Fin C.length) :
    (E.comp H).circuitStep (r.gluedPorts E (C.port (i, side))) =
      r.gluedPorts E ((E.comp G).circuitStep (C.port (i, side))) := by
  obtain ⟨x, hx⟩ := (compPorts E G).surjective (C.port (i, side))
  rcases x with x | x
  · rw [← hx]
    exact r.gluedPorts_left_step E x
  · obtain ⟨p, hp⟩ := h i x hx.symm
    rw [← hx]
    exact r.gluedPorts_right_step E x (r.circuitStep p x hp)

include h in
theorem supported_face_label (i : Fin C.length) :
    Port.label (E.comp H).jointLabel (r.gluedPorts E (C.port (i, side))) =
      Port.label (E.comp G).jointLabel (C.port (i, side)) := by
  obtain ⟨x, hx⟩ := (compPorts E G).surjective (C.port (i, side))
  rcases x with x | x
  · change compLeftEmbedding E G x = C.port (i, side) at hx
    rw [← hx, r.gluedPorts_left, compLeftEmbedding_label, compLeftEmbedding_label]
  · obtain ⟨p, hp⟩ := h i x hx.symm
    change compRightEmbedding E G x = C.port (i, side) at hx
    rw [← hx, r.gluedPorts_right, compRightEmbedding_label, compRightEmbedding_label]
    exact r.labels p x hp

include h in
theorem supported_circuit_pair (i : Fin C.length) :
    (E.comp H).pairing.twin (r.gluedPorts E (C.dart i)) =
      r.gluedPorts E ((E.comp G).pairing.twin (C.dart i)) :=
  C.pairs_of_side (r.gluedPorts E) side (r.supported_face_pair C side h) i

@[reducible] def crossingCircuit : (E.comp H).SimpleCircuit :=
  C.mapAlong (r.gluedPorts E).toEmbedding (r.gluedPorts_vertices E) (r.supported_circuit_pair C side h)

theorem crossingCircuit_port (x : Fin C.length × Bool) :
    (r.crossingCircuit C side h).port x = r.gluedPorts E (C.port x) := C.mapAlong_port _ _ _ x

theorem crossingCircuit_face (hf : C.BoundsFaceOrbit side) :
    (r.crossingCircuit C side h).BoundsFaceOrbit side :=
  C.boundsFaceOrbit_mapAlong (r.gluedPorts E).toEmbedding (r.gluedPorts_vertices E)
    (r.supported_circuit_pair C side h) side hf (r.supported_face_step C side h)

theorem crossingCircuit_face_label (i : Fin C.length) :
    Port.label (E.comp H).jointLabel ((r.crossingCircuit C side h).port (i, side)) =
      Port.label (E.comp G).jointLabel (C.port (i, side)) := by
  rw [r.crossingCircuit_port]
  exact r.supported_face_label C side h i

end BoundaryQuadReplacement
end ThomGame.Pictures.PortGraph
