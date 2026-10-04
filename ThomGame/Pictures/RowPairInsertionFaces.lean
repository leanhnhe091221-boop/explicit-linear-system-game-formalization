module

public import ThomGame.Pictures.RowPairInsertion
public import ThomGame.Pictures.CircuitEmbedding
public import ThomGame.Pictures.CircuitCoverEdges

/-!
# Unaffected circuits in the graph with two inserted row vertices

Every old rotation is retained. A circuit avoiding the two cut labels
has the same actual edges and vertices after insertion; if it bounded
a face orbit or was a label cover, those properties are retained too.
These statements do not require Euler saturation of either graph.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open Equiv
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowPairInsertion) (orientation : Bool)

def oldEmbedding : G.Dart ↪ (s.graph orientation).Dart := ⟨s.old, s.old_injective⟩

theorem old_vertex_iff (x y : G.Dart) :
    (s.old x).vertex = (s.old y).vertex ↔ x.vertex = y.vertex := by
  cases x <;> cases y <;> simp [old, Port.vertex]

theorem rotation_old (x : G.Dart) :
    (s.graph orientation).rotation (s.old x) = s.old (G.rotation x) := by
  cases x <;> rfl

theorem rotation_symm_old (x : G.Dart) :
    (s.graph orientation).rotation.symm (s.old x) = s.old (G.rotation.symm x) := by
  cases x <;> rfl

theorem rotation_fresh (b : Bool) (i : Fin 3) :
    (s.graph orientation).rotation (s.fresh b i) =
      s.fresh b ((if (if b then !orientation else orientation) then
        (finRotate 3).symm else finRotate 3) i) := rfl

theorem twin_old_of_label (x : G.Dart)
    (h₁ : Port.label G.jointLabel x ≠ A.column s.row 1)
    (h₂ : Port.label G.jointLabel x ≠ A.column s.row 2) :
    (s.graph orientation).pairing.twin (s.old x) = s.old (G.pairing.twin x) := by
  apply s.twin_old_away
  · exact fun h => h₁ ((congrArg (Port.label G.jointLabel) h).trans s.first_label)
  · exact fun h => h₂ ((congrArg (Port.label G.jointLabel) h).trans s.second_label)
  · exact fun h => h₁ ((congrArg (Port.label G.jointLabel) h).trans
      ((G.pairing.label_twin _).trans s.first_label))
  · exact fun h => h₂ ((congrArg (Port.label G.jointLabel) h).trans
      ((G.pairing.label_twin _).trans s.second_label))

theorem circuitStep_old_of_label (x : G.Dart)
    (h₁ : Port.label G.jointLabel x ≠ A.column s.row 1)
    (h₂ : Port.label G.jointLabel x ≠ A.column s.row 2) :
    (s.graph orientation).circuitStep (s.old x) = s.old (G.circuitStep x) := by
  rw [(s.graph orientation).circuitStep_apply, s.twin_old_of_label orientation x h₁ h₂,
    s.rotation_old]
  rfl

variable (C : G.SimpleCircuit)
  (havoid : ∀ i, Port.label G.jointLabel (C.dart i) ≠ A.column s.row 1 ∧
    Port.label G.jointLabel (C.dart i) ≠ A.column s.row 2)

@[reducible] def oldCircuit : (s.graph orientation).SimpleCircuit where
  length := C.length
  length_pos := C.length_pos
  dart := C.dart.trans (s.oldEmbedding orientation)
  vertex_injective := fun _ _ h => C.vertex_injective ((s.old_vertex_iff _ _).mp h)
  edge_injective := by
    intro i j h
    apply C.edge_injective
    rcases ((s.graph orientation).pairing.edge_eq_iff _ _).mp h with h | h
    · exact (G.pairing.edge_eq_iff _ _).mpr (Or.inl (s.old_injective h))
    · change s.old (C.dart i) = (s.graph orientation).pairing.twin (s.old (C.dart j)) at h
      rw [s.twin_old_of_label orientation _ (havoid j).1 (havoid j).2] at h
      exact (G.pairing.edge_eq_iff _ _).mpr (Or.inr (s.old_injective h))
  next_vertex := by
    intro i
    change (s.old (C.dart (finRotate C.length i))).vertex =
      ((s.graph orientation).pairing.twin (s.old (C.dart i))).vertex
    rw [s.twin_old_of_label orientation _ (havoid i).1 (havoid i).2]
    exact (s.old_vertex_iff _ _).mpr (C.next_vertex i)
  next_ne_twin := by
    intro i h
    change s.old (C.dart (finRotate C.length i)) =
      (s.graph orientation).pairing.twin (s.old (C.dart i)) at h
    rw [s.twin_old_of_label orientation _ (havoid i).1 (havoid i).2] at h
    exact C.next_ne_twin i (s.old_injective h)

theorem oldCircuit_port (x : Fin C.length × Bool) :
    (s.oldCircuit orientation C havoid).port x = s.old (C.port x) := by
  rcases x with ⟨i, b⟩
  cases b
  · rfl
  · exact s.twin_old_of_label orientation _ (havoid _).1 (havoid _).2

omit orientation in
include havoid in
theorem port_label_avoids (x : Fin C.length × Bool) :
    Port.label G.jointLabel (C.port x) ≠ A.column s.row 1 ∧
      Port.label G.jointLabel (C.port x) ≠ A.column s.row 2 := by
  rcases x with ⟨i, b⟩
  cases b
  · exact havoid i
  · change Port.label G.jointLabel (G.pairing.twin (C.dart _)) ≠ _ ∧
      Port.label G.jointLabel (G.pairing.twin (C.dart _)) ≠ _
    rw [G.pairing.label_twin]
    exact havoid _

theorem oldCircuit_face (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (s.oldCircuit orientation C havoid).BoundsFaceOrbit side := by
  have hs (i : Fin C.length) :
      (s.graph orientation).circuitStep (s.oldEmbedding orientation (C.port (i, side))) =
        s.oldEmbedding orientation (G.circuitStep (C.port (i, side))) :=
    s.circuitStep_old_of_label orientation _ (s.port_label_avoids C havoid _).1
      (s.port_label_avoids C havoid _).2
  intro x
  rw [s.oldCircuit_port]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
    change ((s.graph orientation).circuitStep ^ k) (s.oldEmbedding orientation (C.port (0, side))) = x at hk
    rw [C.face_pow_map (s.oldEmbedding orientation) side hf hs k] at hk
    have hc : G.circuitStep.SameCycle ((G.circuitStep ^ k) (C.port (0, side))) (C.port (0, side)) :=
      (show G.circuitStep.SameCycle (C.port (0, side)) ((G.circuitStep ^ k) (C.port (0, side))) from
        ⟨(k : Int), by simp⟩).symm
    obtain ⟨i, hi⟩ := (hf _).mp hc
    exact ⟨i, (s.oldCircuit_port orientation C havoid (i, side)).trans ((congrArg s.old hi).trans hk)⟩
  · rintro ⟨i, rfl⟩
    rw [s.oldCircuit_port]
    obtain ⟨k, hk⟩ := ((hf _).mpr ⟨i, rfl⟩).symm.exists_nat_pow_eq
    apply Perm.SameCycle.symm
    refine ⟨(k : Int), ?_⟩
    change ((s.graph orientation).circuitStep ^ k) (s.oldEmbedding orientation (C.port (0, side))) = _
    rw [C.face_pow_map (s.oldEmbedding orientation) side hf hs k, hk]
    rfl

theorem oldCircuit_cover (hc : C.IsLabelCover) :
    (s.oldCircuit orientation C havoid).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hx, hy, hne, hl⟩ := hc i
  refine ⟨.inl h, .inl k, p, q, congrArg s.old hx, ?_, ?_, hl⟩
  · change (s.graph orientation).pairing.twin (s.old (C.dart i)) = _
    rw [s.twin_old_of_label orientation _ (havoid i).1 (havoid i).2]
    exact congrArg s.old hy
  · exact fun he => hne (Sum.inl.inj he)

end ThomGame.Pictures.PortGraph.RowPairInsertion
