module

public import ThomGame.Pictures.CircuitEmbedding

/-!
# Embedding a circuit when only interior vertices are preserved

Cutting a region can split an original vertex into distinct boundary
leaves. A simple circuit avoids those leaves. Thus preserving vertex
equality on nonboundary ports suffices to embed the whole circuit.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {u v : List S} {w z : List U} {G : PortGraph P u v} {H : PortGraph Q w z}
  (C : G.SimpleCircuit)

theorem twin_port_not_boundary (x : Fin C.length × Bool) :
    ¬ G.IsBoundary (G.pairing.twin (C.port x)) := by
  rw [C.twin_port]
  exact C.port_not_boundary _ _

/-- An exact face orbit can be reflected through an injective port map
whose face steps commute on the listed side. -/
theorem boundsFaceOrbit_iff_image_orbit (e : G.Dart ↪ H.Dart) (side : Bool)
    (hs : ∀ i, H.circuitStep (e (C.port (i, side))) = e (G.circuitStep (C.port (i, side)))) :
    C.BoundsFaceOrbit side ↔
      ∀ x, H.circuitStep.SameCycle x (e (C.port (0, side))) ↔
        ∃ i, e (C.port (i, side)) = x := by
  constructor
  · intro hf x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
      rw [C.face_pow_map e side hf hs k] at hk
      have hc : G.circuitStep.SameCycle ((G.circuitStep ^ k) (C.port (0, side)))
          (C.port (0, side)) :=
        (show G.circuitStep.SameCycle (C.port (0, side))
          ((G.circuitStep ^ k) (C.port (0, side))) from ⟨(k : Int), by simp⟩).symm
      obtain ⟨i, hi⟩ := (hf _).mp hc
      exact ⟨i, (congrArg e hi).trans hk⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := ((hf _).mpr ⟨i, rfl⟩).symm.exists_nat_pow_eq
      apply Perm.SameCycle.symm
      refine ⟨(k : Int), ?_⟩
      simp only [zpow_natCast, C.face_pow_map e side hf hs, hk]
  · intro hf
    have hpow (k : Nat) : ∃ i,
        (G.circuitStep ^ k) (C.port (0, side)) = C.port (i, side) ∧
        (H.circuitStep ^ k) (e (C.port (0, side))) = e (C.port (i, side)) := by
      induction k with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ k ih =>
        obtain ⟨i, hi, hj⟩ := ih
        have hc : H.circuitStep.SameCycle
            ((H.circuitStep ^ (k + 1)) (e (C.port (0, side)))) (e (C.port (0, side))) :=
          (show H.circuitStep.SameCycle (e (C.port (0, side)))
            ((H.circuitStep ^ (k + 1)) (e (C.port (0, side)))) from
              ⟨((k + 1 : Nat) : Int), by simp only [zpow_natCast]⟩).symm
        obtain ⟨j, he⟩ := (hf _).mp hc
        refine ⟨j, ?_, he.symm⟩
        rw [pow_succ', Perm.mul_apply, hi]
        apply e.injective
        rw [← hs, ← hj, ← Perm.mul_apply, ← pow_succ']
        exact he.symm
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
      obtain ⟨i, hi, _⟩ := hpow k
      exact ⟨i, hi.symm.trans hk⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := ((hf _).mpr ⟨i, rfl⟩).symm.exists_nat_pow_eq
      obtain ⟨j, hj, he⟩ := hpow k
      have hji := e.injective (he.symm.trans hk)
      apply Perm.SameCycle.symm
      exact ⟨(k : Int), by simpa only [zpow_natCast] using hj.trans hji⟩

variable (e : G.Dart ↪ H.Dart)
  (hv : ∀ a b, ¬ G.IsBoundary a → ¬ G.IsBoundary b →
    ((e a).vertex = (e b).vertex ↔ a.vertex = b.vertex))
  (ht : ∀ a, H.pairing.twin (e a) = e (G.pairing.twin a))

@[reducible] def mapInterior : H.SimpleCircuit where
  length := C.length
  length_pos := C.length_pos
  dart := C.dart.trans e
  vertex_injective := fun i j he => C.vertex_injective
    ((hv _ _ (C.port_not_boundary i false) (C.port_not_boundary j false)).mp he)
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
    exact (hv _ _ (C.port_not_boundary _ false) (C.twin_port_not_boundary (i, false))).mpr
      (C.next_vertex i)
  next_ne_twin := by
    intro i he
    change e (C.dart (finRotate C.length i)) = H.pairing.twin (e (C.dart i)) at he
    rw [ht] at he
    exact C.next_ne_twin i (e.injective he)

theorem mapInterior_port (x : Fin C.length × Bool) :
    (C.mapInterior e hv ht).port x = e (C.port x) := by
  rcases x with ⟨i, side⟩
  cases side
  · rfl
  · exact ht _

end ThomGame.Pictures.PortGraph.SimpleCircuit
