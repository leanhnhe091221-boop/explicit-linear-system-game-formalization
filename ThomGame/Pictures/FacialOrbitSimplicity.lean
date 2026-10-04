module

public import ThomGame.Pictures.FacialOrbitCircuit

/-! # A simple facial orbit visits each vertex once and never both ends of an edge -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit) (side : Bool) (hf : C.BoundsFaceOrbit side)

include hf in
theorem face_vertex_injective {x y : G.Dart}
    (hx : G.circuitStep.SameCycle x (C.port (0, side)))
    (hy : G.circuitStep.SameCycle y (C.port (0, side)))
    (hv : x.vertex = y.vertex) : x = y := by
  obtain ⟨i, rfl⟩ := (hf x).mp hx
  obtain ⟨j, rfl⟩ := (hf y).mp hy
  rw [C.port_vertex, C.port_vertex] at hv
  have hij := C.vertex_injective hv
  change i = j at hij
  subst j
  rfl

include hf in
theorem face_rotation_ne_self {x : G.Dart}
    (hx : G.circuitStep.SameCycle x (C.port (0, side))) : G.rotation x ≠ x := by
  obtain ⟨i, rfl⟩ := (hf x).mp hx
  exact C.rotation_port_ne_self i side

include hf in
theorem face_excludes_twin {x : G.Dart}
    (hx : G.circuitStep.SameCycle x (C.port (0, side))) :
    ¬ G.circuitStep.SameCycle (G.pairing.twin x) (C.port (0, side)) := by
  intro ht
  have he := C.face_vertex_injective side hf hx.apply_left ht (G.vertex_circuitStep x)
  exact C.face_rotation_ne_self side hf ht he

end ThomGame.Pictures.PortGraph.SimpleCircuit
