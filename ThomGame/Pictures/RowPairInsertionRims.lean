module

public import ThomGame.Pictures.RowPairInsertionFaces
public import ThomGame.Pictures.OrbitEnumerationTransport
public import ThomGame.Pictures.CoveredRimComponents

/-!
# Complete preservation of other canonical rims under pair insertion

If a cycle avoids all three labels at the inserted row, every retained
dart is old. The old-port embedding is a bijection of complete rim dart
sets and commutes with both pairings and the canonical walk. Thus there
are no new rims of that cycle, and all its facial covers are preserved.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (s : G.RowPairInsertion) (orientation : Bool)
  (C : Hypergraph.Cycle A.hypergraph)
  (havoid : ∀ i : Fin 3, A.column s.row i ∉ Set.range C.edge)

def rimEmbedding : G.RimDart C ↪ (s.graph orientation).RimDart C where
  toFun x := ⟨s.old x.val, by change Port.label G.jointLabel (s.old x.val) ∈ _; rw [s.old_label]; exact x.property⟩
  inj' _ _ h := Subtype.ext (s.old_injective (congrArg Subtype.val h))

include havoid in
theorem rimEmbedding_surjective : Function.Surjective (s.rimEmbedding orientation C) := by
  intro a
  obtain ⟨x, hx⟩ := s.ports.surjective a.val
  rcases x with x | ⟨b, i⟩
  · change s.old x = a.val at hx
    have hm : Port.label G.jointLabel x ∈ Set.range C.edge := by
      rw [← s.old_label x, hx]
      exact a.property
    exact ⟨⟨x, hm⟩, Subtype.ext hx⟩
  · change s.fresh b i = a.val at hx
    have hm : Port.label G.jointLabel (s.fresh b i) ∈ Set.range C.edge := hx.symm ▸ a.property
    rw [s.fresh_label] at hm
    exact (havoid i hm).elim

noncomputable def rimEquiv : G.RimDart C ≃ (s.graph orientation).RimDart C :=
  Equiv.ofBijective (s.rimEmbedding orientation C)
    ⟨(s.rimEmbedding orientation C).injective, s.rimEmbedding_surjective orientation C havoid⟩

theorem rimEquiv_val (a : G.RimDart C) : (s.rimEquiv orientation C havoid a).val = s.old a.val := rfl

theorem rimEquiv_twin (a : G.RimDart C) :
    ((s.graph orientation).rimPairing C).twin (s.rimEquiv orientation C havoid a) =
      s.rimEquiv orientation C havoid ((G.rimPairing C).twin a) :=
  Subtype.ext (s.twin_old_of_label orientation a.val
    (fun he => havoid 1 (he ▸ a.property)) (fun he => havoid 2 (he ▸ a.property)))

theorem rimEquiv_switch (a : G.RimDart C) :
    (s.graph orientation).rimSwitch C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a) =
      s.rimEquiv orientation C havoid (G.rimSwitch C C.empty_boundary_no_rim C.empty_boundary_no_rim a) := by
  apply Eq.symm
  apply (s.graph orientation).rimSwitch_unique
  · exact (s.old_vertex_iff _ _).mpr
      (G.rimSwitch_vertex C C.empty_boundary_no_rim C.empty_boundary_no_rim a)
  · intro he
    exact G.rimSwitch_ne_self C C.empty_boundary_no_rim C.empty_boundary_no_rim a
      ((s.rimEquiv orientation C havoid).injective he)

theorem rimEquiv_walk (a : G.RimDart C) :
    (s.graph orientation).rimWalk C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a) =
      s.rimEquiv orientation C havoid (G.rimWalk C C.empty_boundary_no_rim C.empty_boundary_no_rim a) := by
  change (s.graph orientation).rimSwitch C C.empty_boundary_no_rim C.empty_boundary_no_rim
    (((s.graph orientation).rimPairing C).twin (s.rimEquiv orientation C havoid a)) = _
  rw [s.rimEquiv_twin, s.rimEquiv_switch]
  rfl

theorem rim_length (a : G.RimDart C) :
    (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).length =
      ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a)).length :=
  OrbitEnumeration.length_congr _ _ (s.rimEquiv orientation C havoid)
    (s.rimEquiv_walk orientation C havoid) a

noncomputable def rimIndex (a : G.RimDart C) :
    Fin (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).length ≃
      Fin ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a)).length :=
  finCongr (s.rim_length orientation C havoid a)

theorem rim_dart (a : G.RimDart C)
    (i : Fin (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).length) :
    ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a)).dart (s.rimIndex orientation C havoid a i) =
      s.old ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).dart i) :=
  congrArg Subtype.val (OrbitEnumeration.dart_congr _ _ (s.rimEquiv orientation C havoid)
    (s.rimEquiv_walk orientation C havoid) a i)

include havoid in
omit orientation in
theorem rim_avoids (a : G.RimDart C)
    (i : Fin (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).length) :
    Port.label G.jointLabel ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).dart i) ≠
        A.column s.row 1 ∧
      Port.label G.jointLabel ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).dart i) ≠
        A.column s.row 2 := by
  have hm := G.rimSimpleCircuit_rim C C.empty_boundary_no_rim C.empty_boundary_no_rim a i
  exact ⟨fun he => havoid 1 (he ▸ hm), fun he => havoid 2 (he ▸ hm)⟩

theorem rim_port (a : G.RimDart C)
    (i : Fin (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).length) (b : Bool) :
    ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
        (s.rimEquiv orientation C havoid a)).port (s.rimIndex orientation C havoid a i, b) =
      s.old ((G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).port (i, b)) := by
  cases b
  · exact s.rim_dart orientation C havoid a i
  · have hi {m n : Nat} (he : m = n) (j : Fin m) :
        (finRotate n).symm (finCongr he j) = finCongr he ((finRotate m).symm j) := by subst n; rfl
    change (s.graph orientation).pairing.twin
      ((s.graph orientation).rimSimpleCircuit C _ _ _ |>.dart
        ((finRotate _).symm (finCongr (s.rim_length orientation C havoid a) i))) = _
    rw [hi]
    change (s.graph orientation).pairing.twin
      ((s.graph orientation).rimSimpleCircuit C _ _ _ |>.dart
        (s.rimIndex orientation C havoid a ((finRotate _).symm i))) = _
    rw [s.rim_dart]
    exact s.twin_old_of_label orientation _ (s.rim_avoids C havoid a _).1 (s.rim_avoids C havoid a _).2

theorem rim_face (a : G.RimDart C) (b : Bool)
    (hf : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).BoundsFaceOrbit b) :
    ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
      (s.rimEquiv orientation C havoid a)).BoundsFaceOrbit b := by
  let L := G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a
  let K := (s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
    (s.rimEquiv orientation C havoid a)
  let D := s.oldCircuit orientation L (s.rim_avoids C havoid a)
  have hd : D.BoundsFaceOrbit b := s.oldCircuit_face orientation L _ b hf
  have hp (i : Fin L.length) : K.port (s.rimIndex orientation C havoid a i, b) = D.port (i, b) :=
    (s.rim_port orientation C havoid a i b).trans (s.oldCircuit_port orientation L _ (i, b)).symm
  have h0 : K.port (0, b) = D.port (0, b) := hp 0
  intro x
  change (s.graph orientation).circuitStep.SameCycle x (K.port (0, b)) ↔ ∃ i, K.port (i, b) = x
  rw [h0, hd]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨s.rimIndex orientation C havoid a i, (hp i).trans hi⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, rfl⟩ := (s.rimIndex orientation C havoid a).surjective j
    exact ⟨i, (hp i).symm.trans hj⟩

theorem rim_cover (a : G.RimDart C)
    (hc : (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).IsLabelCover) :
    ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim
      (s.rimEquiv orientation C havoid a)).IsLabelCover := by
  intro j
  obtain ⟨i, rfl⟩ := (s.rimIndex orientation C havoid a).surjective j
  obtain ⟨h, k, p, q, hx, hy, hne, hl⟩ := hc i
  have hd := s.rim_dart orientation C havoid a i
  refine ⟨.inl h, .inl k, p, q, hd.trans (congrArg s.old hx), ?_,
    fun he => hne (Sum.inl.inj he), hl⟩
  rw [hd, s.twin_old_of_label orientation _ (s.rim_avoids C havoid a i).1 (s.rim_avoids C havoid a i).2]
  exact congrArg s.old hy

include havoid in
theorem all_rims_facial_covers
    (hf : ∀ a : G.RimDart C,
      (∃ b, (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).BoundsFaceOrbit b) ∧
        (G.rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).IsLabelCover) :
    ∀ a : (s.graph orientation).RimDart C,
      (∃ b, ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).BoundsFaceOrbit b) ∧
        ((s.graph orientation).rimSimpleCircuit C C.empty_boundary_no_rim C.empty_boundary_no_rim a).IsLabelCover := by
  intro a
  obtain ⟨a, rfl⟩ := (s.rimEquiv orientation C havoid).surjective a
  obtain ⟨⟨b, hb⟩, hc⟩ := hf a
  exact ⟨⟨b, s.rim_face orientation C havoid a b hb⟩, s.rim_cover orientation C havoid a hc⟩

end ThomGame.Pictures.PortGraph.RowPairInsertion
