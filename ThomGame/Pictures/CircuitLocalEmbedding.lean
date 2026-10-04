module

public import ThomGame.Pictures.CircuitEmbedding

/-!
# Transporting a simple facial circuit using only its own edge pairs

Only the listed circuit edges must retain their pairing. Unrelated
parts of the ambient graph may change. The exact face orbit is retained
when its individual face steps commute with the embedding.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {u v : List S} {w z : List U} {G : PortGraph P u v} {H : PortGraph Q w z}

theorem vertex_iff_of_rotation_equiv (e : G.Dart ≃ H.Dart)
    (hr : ∀ x, H.rotation (e x) = e (G.rotation x)) (a b : G.Dart) :
    (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex := by
  rw [← H.rotation_sameCycle_iff, ← G.rotation_sameCycle_iff]
  exact (FiniteReturn.sameCycle_congr _ _ e hr a b).symm

namespace SimpleCircuit

theorem pairs_of_side (C : G.SimpleCircuit) (e : G.Dart → H.Dart) (side : Bool)
    (ht : ∀ i, H.pairing.twin (e (C.port (i, side))) = e (G.pairing.twin (C.port (i, side)))) :
    ∀ i, H.pairing.twin (e (C.dart i)) = e (G.pairing.twin (C.dart i)) := by
  cases side with
  | false => exact ht
  | true =>
    intro i
    have hp := ht (finRotate C.length i)
    change H.pairing.twin (e (G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length i))))) =
      e (G.pairing.twin (G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length i))))) at hp
    rw [Equiv.symm_apply_apply, G.pairing.involutive] at hp
    exact (congrArg H.pairing.twin hp.symm).trans (H.pairing.involutive _)

variable (C : G.SimpleCircuit) (e : G.Dart ↪ H.Dart)
  (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
  (ht : ∀ i, H.pairing.twin (e (C.dart i)) = e (G.pairing.twin (C.dart i)))

@[reducible] def mapAlong : H.SimpleCircuit where
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
    change (e (C.dart (finRotate C.length i))).vertex = (H.pairing.twin (e (C.dart i))).vertex
    rw [ht]
    exact (hv _ _).mpr (C.next_vertex i)
  next_ne_twin := by
    intro i he
    change e (C.dart (finRotate C.length i)) = H.pairing.twin (e (C.dart i)) at he
    rw [ht] at he
    exact C.next_ne_twin i (e.injective he)

theorem mapAlong_port (x : Fin C.length × Bool) :
    (C.mapAlong e hv ht).port x = e (C.port x) := by
  rcases x with ⟨i, side⟩
  cases side
  · rfl
  · exact ht _

theorem boundsFaceOrbit_mapAlong (side : Bool) (hf : C.BoundsFaceOrbit side)
    (hs : ∀ i, H.circuitStep (e (C.port (i, side))) = e (G.circuitStep (C.port (i, side)))) :
    (C.mapAlong e hv ht).BoundsFaceOrbit side := by
  intro x
  change H.circuitStep.SameCycle x ((C.mapAlong e hv ht).port ((0 : Fin C.length), side)) ↔
    ∃ i : Fin C.length, (C.mapAlong e hv ht).port (i, side) = x
  rw [C.mapAlong_port e hv ht (0, side)]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
    rw [C.face_pow_map e side hf hs k] at hk
    have hc : G.circuitStep.SameCycle ((G.circuitStep ^ k) (C.port (0, side)))
        (C.port (0, side)) := (show G.circuitStep.SameCycle (C.port (0, side))
          ((G.circuitStep ^ k) (C.port (0, side))) from ⟨(k : Int), by simp⟩).symm
    obtain ⟨i, hi⟩ := (hf _).mp hc
    exact ⟨i, (C.mapAlong_port e hv ht (i, side)).trans ((congrArg e hi).trans hk)⟩
  · rintro ⟨i, rfl⟩
    rw [C.mapAlong_port e hv ht]
    obtain ⟨k, hk⟩ := ((hf _).mpr ⟨i, rfl⟩).symm.exists_nat_pow_eq
    apply Perm.SameCycle.symm
    refine ⟨(k : Int), ?_⟩
    simp only [zpow_natCast, C.face_pow_map e side hf hs, hk]

end SimpleCircuit
end ThomGame.Pictures.PortGraph
