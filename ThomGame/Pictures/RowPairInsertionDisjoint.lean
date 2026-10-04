module

public import ThomGame.Pictures.RowPairInsertionFaces
public import ThomGame.Pictures.CircuitLocalEmbedding

/-!
# Circuits disjoint from the actual cut ports survive pair insertion

Avoidance is stated for the two selected edges themselves, rather than
their labels. This preserves other components of the same labelled rim.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowPairInsertion) (o : Bool)
  (C : G.SimpleCircuit) (ha : ¬ C.Marked s.first) (hb : ¬ C.Marked s.second)

include ha hb in
theorem twin_old_of_marked {x : G.Dart} (hx : C.Marked x) :
    (s.graph o).pairing.twin (s.old x) = s.old (G.pairing.twin x) := by
  apply s.twin_old_away
  · exact fun he => ha (he ▸ hx)
  · exact fun he => hb (he ▸ hx)
  · exact fun he => ha ((C.marked_twin_iff s.first).mp (he ▸ hx))
  · exact fun he => hb ((C.marked_twin_iff s.second).mp (he ▸ hx))

@[reducible] noncomputable def disjointCircuit : (s.graph o).SimpleCircuit :=
  C.mapAlong (s.oldEmbedding o) s.old_vertex_iff
    (fun i => s.twin_old_of_marked o C ha hb ⟨(i, false), rfl⟩)

theorem disjointCircuit_port (x : Fin C.length × Bool) :
    (s.disjointCircuit o C ha hb).port x = s.old (C.port x) :=
  C.mapAlong_port _ _ _ x

theorem disjointCircuit_marked (x : G.Dart) :
    (s.disjointCircuit o C ha hb).Marked (s.old x) ↔ C.Marked x := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, s.old_injective ((s.disjointCircuit_port o C ha hb i).symm.trans hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, s.disjointCircuit_port o C ha hb i⟩

theorem disjointCircuit_face (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (s.disjointCircuit o C ha hb).BoundsFaceOrbit side := by
  apply C.boundsFaceOrbit_mapAlong _ _ _ side hf
  intro i
  change (s.graph o).circuitStep (s.old (C.port (i, side))) = s.old (G.circuitStep (C.port (i, side)))
  rw [(s.graph o).circuitStep_apply, s.twin_old_of_marked o C ha hb ⟨(i, side), rfl⟩,
    s.rotation_old]
  rfl

theorem disjointCircuit_cover (hc : C.IsLabelCover) :
    (s.disjointCircuit o C ha hb).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hx, hy, hne, hl⟩ := hc i
  refine ⟨.inl h, .inl k, p, q, congrArg s.old hx, ?_, fun he => hne (Sum.inl.inj he), hl⟩
  change (s.graph o).pairing.twin (s.old (C.dart i)) = _
  exact (s.twin_old_of_marked o C ha hb (x := C.dart i) ⟨(i, false), rfl⟩).trans
    (congrArg s.old hy)

end ThomGame.Pictures.PortGraph.RowPairInsertion
