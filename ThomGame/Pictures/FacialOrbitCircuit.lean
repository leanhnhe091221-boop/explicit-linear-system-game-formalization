module

public import ThomGame.Pictures.CircuitEmbedding
public import ThomGame.Pictures.OrbitEnumeration

/-!
# A face orbit with distinct incident vertices is a simple circuit

Excluding fixed rotations rules out one-valent backtracking. Enumerating
the actual face permutation then gives a simple circuit with exactly
that face orbit. This is useful after suppressing degree-two vertices.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v}

theorem rotation_ne_self_of_vertex {x y : G.Dart} (hv : x.vertex = y.vertex) (hne : x ≠ y) :
    G.rotation x ≠ x := by
  intro he
  have hp : ∀ n : Nat, (G.rotation ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, he]
  obtain ⟨n, hn⟩ := ((G.rotation_sameCycle_iff x y).mpr hv).exists_nat_pow_eq
  exact hne ((hp n).symm.trans hn)

theorem SimpleCircuit.rotation_port_ne_self (C : G.SimpleCircuit) (i : Fin C.length) (side : Bool) :
    G.rotation (C.port (i, side)) ≠ C.port (i, side) := by
  apply rotation_ne_self_of_vertex ((C.port_vertex (i, side)).trans (C.port_vertex (i, !side)).symm)
  intro he
  have hb := congrArg Prod.snd (C.port_injective he)
  cases side <;> cases hb

variable (G) (a : G.Dart)
  (hv : ∀ x y, G.circuitStep.SameCycle x a → G.circuitStep.SameCycle y a → x.vertex = y.vertex → x = y)
  (hr : ∀ x, G.circuitStep.SameCycle x a → G.rotation x ≠ x)

@[reducible] noncomputable def facialCircuitOfOrbit : G.SimpleCircuit where
  length := OrbitEnumeration.length G.circuitStep a
  length_pos := OrbitEnumeration.length_pos G.circuitStep a
  dart := OrbitEnumeration.dart G.circuitStep a
  vertex_injective := by
    intro i j he
    apply (OrbitEnumeration.dart G.circuitStep a).injective
    exact hv _ _ (OrbitEnumeration.dart_sameCycle _ _ i).symm
      (OrbitEnumeration.dart_sameCycle _ _ j).symm he
  edge_injective := by
    intro i j he
    rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
    · exact (OrbitEnumeration.dart G.circuitStep a).injective he
    · have hi := (OrbitEnumeration.dart_sameCycle G.circuitStep a i).symm
      have hj := (OrbitEnumeration.dart_sameCycle G.circuitStep a j).symm
      have hri : G.circuitStep.SameCycle (G.rotation (OrbitEnumeration.dart G.circuitStep a i)) a := by
        rw [he]
        exact hj.apply_left
      exact (hr _ hi (hv _ _ hri hi (G.vertex_rotation _))).elim
  next_vertex := fun i => (congrArg Port.vertex (OrbitEnumeration.dart_next G.circuitStep a i)).trans
    (G.vertex_circuitStep _)
  next_ne_twin := by
    intro i he
    have hi := (OrbitEnumeration.dart_sameCycle G.circuitStep a i).symm
    have hn := (OrbitEnumeration.dart_sameCycle G.circuitStep a
      (finRotate (OrbitEnumeration.length G.circuitStep a) i)).symm.apply_left
    rw [he] at hn
    change G.circuitStep.SameCycle (G.rotation (G.pairing.twin (G.pairing.twin _))) a at hn
    rw [G.pairing.involutive] at hn
    exact hr _ hi (hv _ _ hn hi (G.vertex_rotation _))

theorem facialCircuitOfOrbit_face : (G.facialCircuitOfOrbit a hv hr).BoundsFaceOrbit false := by
  intro x
  change G.circuitStep.SameCycle x a ↔ ∃ i, OrbitEnumeration.dart G.circuitStep a i = x
  exact ⟨fun h => (OrbitEnumeration.dart_range _ _ x).mpr h.symm,
    fun h => ((OrbitEnumeration.dart_range _ _ x).mp h).symm⟩

end ThomGame.Pictures.PortGraph
