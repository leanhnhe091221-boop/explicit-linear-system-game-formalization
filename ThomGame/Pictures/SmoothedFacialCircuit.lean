module

public import ThomGame.Pictures.FacialOrbitCircuit
public import ThomGame.Pictures.SmoothedCircuitCovers

/-!
# Suppressing joints in an arbitrary simple facial circuit

The circuit may run through joints, including newly glued seam vertices.
If at least one of its face ports is terminal, full smoothing retains a
simple facial circuit. Its listed ports are exactly the original face
ports that survive, each once. Label-cover hypotheses are unnecessary.
-/

@[expose] public section
namespace ThomGame.Pictures

open PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} {circles : List S}

namespace PortGraph.SimpleCircuit

variable (C : G.SimpleCircuit) (side : Bool) (hf : C.BoundsFaceOrbit side)
  (t : Smoothing G H circles) [IsEmpty H.Joint]
  (i₀ : Fin C.length) (ha : G.Terminal (C.port (i₀, side)))

noncomputable def reducedFaceBase : H.Dart := t.liftTerminal ⟨C.port (i₀, side), ha⟩

include hf in
theorem reduced_face_iff (x : H.Dart) :
    H.circuitStep.SameCycle x (C.reducedFaceBase side t i₀ ha) ↔
      ∃ i, t.portEmbedding x = C.port (i, side) := by
  rw [← H.circuit_eq_iff, t.sameCircuit_iff, G.circuit_eq_iff]
  have hb : t.portEmbedding (C.reducedFaceBase side t i₀ ha) = C.port (i₀, side) :=
    t.portEmbedding_liftTerminal _
  rw [hb]
  have hi := (hf _).mpr ⟨i₀, rfl⟩
  constructor
  · intro hx
    obtain ⟨i, he⟩ := (hf _).mp (hx.trans hi)
    exact ⟨i, he.symm⟩
  · rintro ⟨i, he⟩
    exact ((hf _).mpr ⟨i, he.symm⟩).trans hi.symm

include hf in
theorem reduced_face_vertices (x y : H.Dart)
    (hx : H.circuitStep.SameCycle x (C.reducedFaceBase side t i₀ ha))
    (hy : H.circuitStep.SameCycle y (C.reducedFaceBase side t i₀ ha))
    (hv : x.vertex = y.vertex) : x = y := by
  obtain ⟨i, hi⟩ := (C.reduced_face_iff side hf t i₀ ha x).mp hx
  obtain ⟨j, hj⟩ := (C.reduced_face_iff side hf t i₀ ha y).mp hy
  have hxy := (t.portEmbedding_vertex_iff x y).mp hv
  rw [hi, hj, C.port_vertex, C.port_vertex] at hxy
  have hij := C.vertex_injective hxy
  change i = j at hij
  subst j
  exact t.portEmbedding.injective (hi.trans hj.symm)

include hf in
theorem reduced_face_rotation (x : H.Dart)
    (hx : H.circuitStep.SameCycle x (C.reducedFaceBase side t i₀ ha)) : H.rotation x ≠ x := by
  obtain ⟨i, hi⟩ := (C.reduced_face_iff side hf t i₀ ha x).mp hx
  intro he
  have hr := congrArg t.portEmbedding he
  rw [t.portRotation, hi] at hr
  exact C.rotation_port_ne_self i side hr

@[reducible] noncomputable def reducedFacialCircuit : H.SimpleCircuit :=
  H.facialCircuitOfOrbit (C.reducedFaceBase side t i₀ ha)
    (C.reduced_face_vertices side hf t i₀ ha) (C.reduced_face_rotation side hf t i₀ ha)

theorem reducedFacialCircuit_face : (C.reducedFacialCircuit side hf t i₀ ha).BoundsFaceOrbit false :=
  H.facialCircuitOfOrbit_face _ _ _

theorem reducedFacialCircuit_dart_original (j : Fin (C.reducedFacialCircuit side hf t i₀ ha).length) :
    ∃ i, t.portEmbedding ((C.reducedFacialCircuit side hf t i₀ ha).dart j) = C.port (i, side) :=
  (C.reduced_face_iff side hf t i₀ ha _).mp (OrbitEnumeration.dart_sameCycle _ _ j).symm

theorem reducedFacialCircuit_complete (i : Fin C.length) (hi : G.Terminal (C.port (i, side))) :
    ∃! j : Fin (C.reducedFacialCircuit side hf t i₀ ha).length,
      t.portEmbedding ((C.reducedFacialCircuit side hf t i₀ ha).dart j) = C.port (i, side) := by
  let x := t.liftTerminal ⟨C.port (i, side), hi⟩
  have hx : t.portEmbedding x = C.port (i, side) := t.portEmbedding_liftTerminal _
  have hc := (C.reduced_face_iff side hf t i₀ ha x).mpr ⟨i, hx⟩
  obtain ⟨j, hj⟩ := (OrbitEnumeration.dart_range _ _ x).mpr hc.symm
  refine ⟨j, (congrArg t.portEmbedding hj).trans hx, ?_⟩
  intro k hk
  exact (C.reducedFacialCircuit side hf t i₀ ha).dart.injective
    (t.portEmbedding.injective (hk.trans ((congrArg t.portEmbedding hj).trans hx).symm))

end PortGraph.SimpleCircuit
end ThomGame.Pictures
