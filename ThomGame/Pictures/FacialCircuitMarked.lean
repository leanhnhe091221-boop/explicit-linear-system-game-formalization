module

public import ThomGame.Pictures.SmoothedFacialCircuit

/-!
# Unoriented circuit edges and their survival under smoothing

A marked edge has one port on either chosen side of its circuit.
For a facial circuit this identifies its marked ports using its face
orbit and the opposite edge port. Smoothing preserves that unoriented
membership, including when the opposite original port is a seam joint.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} {cs : List S}

namespace PortGraph.SimpleCircuit

variable (C : G.SimpleCircuit)

theorem marked_iff_side_or_twin (side : Bool) (x : G.Dart) :
    C.Marked x ↔ (∃ i, C.port (i, side) = x) ∨ (∃ i, C.port (i, side) = G.pairing.twin x) := by
  constructor
  · rintro ⟨⟨i, s⟩, rfl⟩
    by_cases he : s = side
    · subst s
      exact Or.inl ⟨i, rfl⟩
    · right
      have hn : (!s) = side := by cases s <;> cases side <;> simp_all
      refine ⟨(CircuitPermutations.edge C.length (i, s)).1, ?_⟩
      have ht := C.twin_port (i, s)
      have hp : CircuitPermutations.edge C.length (i, s) =
          ((CircuitPermutations.edge C.length (i, s)).1, side) :=
        Prod.ext rfl ((CircuitPermutations.edge_snd C.length (i, s)).trans hn)
      rw [hp] at ht
      exact ht.symm
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨(i, side), hi⟩
    · exact (C.marked_twin_iff x).mp ⟨(i, side), hi⟩

theorem marked_iff_face_or_twin (side : Bool) (hf : C.BoundsFaceOrbit side) (x : G.Dart) :
    C.Marked x ↔ G.circuitStep.SameCycle x (C.port (0, side)) ∨
      G.circuitStep.SameCycle (G.pairing.twin x) (C.port (0, side)) := by
  rw [C.marked_iff_side_or_twin side x, hf x, hf (G.pairing.twin x)]

end PortGraph.SimpleCircuit

namespace Smoothing

variable (t : Smoothing G H cs)

theorem sameCycle_portEmbedding (a b : H.Dart) :
    G.circuitStep.SameCycle (t.portEmbedding a) (t.portEmbedding b) ↔ H.circuitStep.SameCycle a b := by
  rw [← G.circuit_eq_iff, ← t.sameCircuit_iff, H.circuit_eq_iff]

theorem sameCycle_twin_portEmbedding (a b : H.Dart) :
    G.circuitStep.SameCycle (G.pairing.twin (t.portEmbedding a)) (t.portEmbedding b) ↔
      H.circuitStep.SameCycle (H.pairing.twin a) b := by
  have hg : G.circuitStep (G.pairing.twin (t.portEmbedding a)) = t.portEmbedding (H.rotation a) := by
    rw [G.circuitStep_apply, G.pairing.involutive, t.portRotation]
  have hh : H.circuitStep (H.pairing.twin a) = H.rotation a := by
    rw [H.circuitStep_apply, H.pairing.involutive]
  calc
    _ ↔ G.circuitStep.SameCycle (G.circuitStep (G.pairing.twin (t.portEmbedding a)))
        (t.portEmbedding b) := Perm.sameCycle_apply_left.symm
    _ ↔ H.circuitStep.SameCycle (H.rotation a) b := by rw [hg, t.sameCycle_portEmbedding]
    _ ↔ _ := by rw [← hh]; exact Perm.sameCycle_apply_left

end Smoothing

namespace PortGraph.SimpleCircuit

variable (C : G.SimpleCircuit) (side : Bool) (hf : C.BoundsFaceOrbit side)
  (t : Smoothing G H cs) [IsEmpty H.Joint]
  (i₀ : Fin C.length) (ha : G.Terminal (C.port (i₀, side)))

theorem reducedFacialCircuit_marked_iff (x : H.Dart) :
    (C.reducedFacialCircuit side hf t i₀ ha).Marked x ↔ C.Marked (t.portEmbedding x) := by
  let F := C.reducedFacialCircuit side hf t i₀ ha
  have hbase : F.port (0, false) = C.reducedFaceBase side t i₀ ha := rfl
  have hbase' : t.portEmbedding (C.reducedFaceBase side t i₀ ha) = C.port (i₀, side) :=
    t.portEmbedding_liftTerminal _
  have hanchor := (hf _).mpr ⟨i₀, rfl⟩
  have hs (a : G.Dart) : G.circuitStep.SameCycle a (C.port (i₀, side)) ↔
      G.circuitStep.SameCycle a (C.port (0, side)) :=
    ⟨fun h => h.trans hanchor, fun h => h.trans hanchor.symm⟩
  rw [F.marked_iff_face_or_twin false (C.reducedFacialCircuit_face side hf t i₀ ha),
    C.marked_iff_face_or_twin side hf, hbase]
  rw [← t.sameCycle_portEmbedding x, ← t.sameCycle_twin_portEmbedding x,
    hbase', hs, hs]

end PortGraph.SimpleCircuit
end ThomGame.Pictures
