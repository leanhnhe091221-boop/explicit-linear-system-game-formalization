module

public import ThomGame.Pictures.CircuitFaces

/-!
# Faciality is independent of the enumeration of a simple circuit

Two simple circuits with the same actual marked ports have the same
length. In an Euler-saturated graph, a facial side of either circuit
gives a facial side of the other, without fixing an orientation.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C D : G.SimpleCircuit)
  (hM : ∀ x : G.Dart, C.Marked x ↔ D.Marked x)

include hM in
theorem length_eq_of_marked_iff : C.length = D.length := by
  have he : C.Marked = D.Marked := funext (fun x => propext (hM x))
  have hc := C.marked_card
  rw [he, D.marked_card] at hc
  omega

include hM in
theorem exists_port_zero_on_side (side : Bool) :
    ∃ (s : Bool) (k : Fin D.length), C.port (0, s) = D.port (k, side) := by
  obtain ⟨⟨k, t⟩, hk⟩ := (hM (C.port (0, false))).mp ⟨(0, false), rfl⟩
  obtain ⟨⟨l, s⟩, hl⟩ := (hM (D.port (k, side))).mpr ⟨(k, side), rfl⟩
  have hv : (C.dart l).vertex = (C.dart 0).vertex :=
    (C.port_vertex (l, s)).symm.trans ((congrArg Port.vertex hl).trans
      ((D.port_vertex (k, side)).trans ((D.port_vertex (k, t)).symm.trans
        (congrArg Port.vertex hk))))
  have he : l = 0 := C.vertex_injective hv
  exact ⟨s, k, he ▸ hl⟩

include hM in
theorem exists_face_of_marked_iff
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (side : Bool) (hD : D.BoundsFaceOrbit side) : ∃ s, C.BoundsFaceOrbit s := by
  obtain ⟨s, k, he⟩ := C.exists_port_zero_on_side D hM side
  have hanchor : G.circuitStep.SameCycle (C.port (0, s)) (D.port (0, side)) := by
    rw [he]
    exact (hD _).mpr ⟨k, rfl⟩
  let M (x : G.Dart) : Prop := G.circuitStep.SameCycle x (D.port (0, side))
  have hmark (x : G.Dart) (hx : M x) : C.Marked x := by
    obtain ⟨l, hl⟩ := (hD x).mp hx
    exact (hM x).mpr ⟨(l, side), hl⟩
  have hp (x : G.Dart) (hx : M x) : M (G.circuitStep x) := hx.apply_left
  have ht (x : G.Dart) (hx : M x) : M (C.cutPairing x) := by
    rw [C.cutPairing_of_marked (hmark x hx)]
    exact hx
  refine ⟨s, C.boundsFaceOrbit_of_closed hEuler s ?_⟩
  intro x _ hx
  exact hmark x (hx.symm.predicate_of_forward M hp ht hanchor)

end ThomGame.Pictures.PortGraph.SimpleCircuit
