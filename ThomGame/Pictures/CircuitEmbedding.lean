module

public import ThomGame.Pictures.CircuitFaces

/-!
# Simple circuits and their exact face orbits under port embeddings

An injective map preserving paired ports and equality of incident vertices
transports an actual simple circuit. To preserve one of its face orbits,
the face step need only commute on that side's ports. No global graph
isomorphism or placement of unrelated components is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {u v : List S} {w z : List U} {G : PortGraph P u v} {H : PortGraph Q w z}

theorem eq_of_boundary_vertex {a b : G.Dart} (ha : G.IsBoundary a)
    (hv : b.vertex = a.vertex) : b = a := by
  cases a <;> cases b <;> simp_all [IsBoundary, Port.vertex]

namespace SimpleCircuit

variable (C : G.SimpleCircuit)

theorem port_not_boundary (i : Fin C.length) (side : Bool) :
    ¬ G.IsBoundary (C.port (i, side)) := by
  intro hb
  have hi := eq_of_boundary_vertex hb
    ((C.incoming_vertex i).trans (C.port_vertex (i, side)).symm)
  have ho := eq_of_boundary_vertex hb (C.port_vertex (i, side)).symm
  exact C.incoming_ne_outgoing i (hi.trans ho.symm)

variable (e : G.Dart ↪ H.Dart)
  (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
  (ht : ∀ a, H.pairing.twin (e a) = e (G.pairing.twin a))

/-- Transport the listed edges and vertices along the actual port embedding. -/
@[reducible] def map : H.SimpleCircuit where
  length := C.length
  length_pos := C.length_pos
  dart := C.dart.trans e
  vertex_injective := fun i j he => C.vertex_injective ((hv _ _).mp he)
  edge_injective := by
    intro i j he
    apply C.edge_injective
    rcases (H.pairing.edge_eq_iff _ _).mp he with he | he
    · exact (G.pairing.edge_eq_iff _ _).mpr (Or.inl (e.injective he))
    · change e (C.dart i) = H.pairing.twin (e (C.dart j)) at he
      rw [ht] at he
      exact (G.pairing.edge_eq_iff _ _).mpr (Or.inr (e.injective he))
  next_vertex := by
    intro i
    change (e (C.dart (finRotate C.length i))).vertex =
      (H.pairing.twin (e (C.dart i))).vertex
    rw [ht]
    exact (hv _ _).mpr (C.next_vertex i)
  next_ne_twin := by
    intro i he
    change e (C.dart (finRotate C.length i)) = H.pairing.twin (e (C.dart i)) at he
    rw [ht] at he
    exact C.next_ne_twin i (e.injective he)

theorem map_dart (i : Fin C.length) : (C.map e hv ht).dart i = e (C.dart i) := rfl

theorem map_port (x : Fin C.length × Bool) :
    (C.map e hv ht).port x = e (C.port x) := by
  rcases x with ⟨i, side⟩
  cases side
  · rfl
  · exact ht _

variable (side : Bool) (hf : C.BoundsFaceOrbit side)
  (hs : ∀ i, H.circuitStep (e (C.port (i, side))) = e (G.circuitStep (C.port (i, side))))

include hf hs in
theorem face_pow_map (k : Nat) :
    (H.circuitStep ^ k) (e (C.port (0, side))) =
      e ((G.circuitStep ^ k) (C.port (0, side))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    have hc : G.circuitStep.SameCycle ((G.circuitStep ^ k) (C.port (0, side)))
        (C.port (0, side)) := (show G.circuitStep.SameCycle (C.port (0, side))
          ((G.circuitStep ^ k) (C.port (0, side))) from ⟨(k : Int), by simp⟩).symm
    obtain ⟨i, hi⟩ := (hf _).mp hc
    rw [← hi]
    exact hs i

include hf hs in
theorem boundsFaceOrbit_map : (C.map e hv ht).BoundsFaceOrbit side := by
  intro x
  change H.circuitStep.SameCycle x ((C.map e hv ht).port ((0 : Fin C.length), side)) ↔
    ∃ i : Fin C.length, (C.map e hv ht).port (i, side) = x
  have hp := C.map_port e hv ht (0, side)
  rw [hp]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
    rw [C.face_pow_map e side hf hs k] at hk
    have hc : G.circuitStep.SameCycle ((G.circuitStep ^ k) (C.port (0, side)))
        (C.port (0, side)) := (show G.circuitStep.SameCycle (C.port (0, side))
          ((G.circuitStep ^ k) (C.port (0, side))) from ⟨(k : Int), by simp⟩).symm
    obtain ⟨i, hi⟩ := (hf _).mp hc
    exact ⟨i, (C.map_port e hv ht (i, side)).trans ((congrArg e hi).trans hk)⟩
  · rintro ⟨i, rfl⟩
    rw [C.map_port e hv ht]
    obtain ⟨k, hk⟩ := ((hf _).mpr ⟨i, rfl⟩).symm.exists_nat_pow_eq
    apply Perm.SameCycle.symm
    refine ⟨(k : Int), ?_⟩
    simp only [zpow_natCast, C.face_pow_map e side hf hs, hk]

end SimpleCircuit
end ThomGame.Pictures.PortGraph
