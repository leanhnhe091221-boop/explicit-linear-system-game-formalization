module

public import ThomGame.Pictures.RowGraphEmbeddingCircuits
public import ThomGame.Pictures.OrbitEnumerationTransport

/-!
# Every canonical rim circuit is retained by an open row embedding

When the target cycle labels pull back exactly to the source cycle labels,
the full rim dart sets are equivalent. Their edge pairings and unique
continuations at vertices commute, hence their canonical orbit lengths
and enumerated simple circuits agree under explicit index transport.
Both the exact face-orbit property and label coverage transfer to the
canonical target circuits, not merely to a selected family of curves.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S T U : Type*} [DecidableEq R] [DecidableEq S] [DecidableEq T] [DecidableEq U]
  {A : SparseSystem R S} {B : SparseSystem T U} {u v : List S}
  (G : SolutionGroup.RowGraph A u v) (ι : A.hypergraph.OpenEmbedding B.hypergraph)
  (C : Hypergraph.Cycle A.hypergraph) (D : Hypergraph.Cycle B.hypergraph)
  (hR : ∀ x : S, ι.edge x ∈ Set.range D.edge ↔ x ∈ Set.range C.edge)

include hR in
theorem embeddedRim_no_boundary {w : List S} (hw : ∀ x ∈ w, x ∉ Set.range C.edge) :
    ∀ x ∈ w.map ι.edge, x ∉ Set.range D.edge := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact fun hd => hw y hy ((hR y).mp hd)

include hR in
theorem rowEmbedding_rim_iff (a : G.Dart) :
    Port.label (G.embedRows ι).jointLabel (G.rowEmbeddingPorts ι a) ∈ Set.range D.edge ↔
      Port.label G.jointLabel a ∈ Set.range C.edge := by
  rw [G.rowEmbeddingPorts_label]
  exact hR _

noncomputable def embeddedRimEquiv : G.RimDart C ≃ (G.embedRows ι).RimDart D where
  toFun a := ⟨G.rowEmbeddingPorts ι a.val, (G.rowEmbedding_rim_iff ι C D hR a.val).mpr a.property⟩
  invFun a := ⟨(G.rowEmbeddingPorts ι).symm a.val,
    (G.rowEmbedding_rim_iff ι C D hR _).mp (by rw [Equiv.apply_symm_apply]; exact a.property)⟩
  left_inv a := Subtype.ext ((G.rowEmbeddingPorts ι).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((G.rowEmbeddingPorts ι).apply_symm_apply a.val)

theorem embeddedRimEquiv_val (a : G.RimDart C) :
    (G.embeddedRimEquiv ι C D hR a).val = G.rowEmbeddingPorts ι a.val := rfl

theorem embeddedRimEquiv_twin (a : G.RimDart C) :
    ((G.embedRows ι).rimPairing D).twin (G.embeddedRimEquiv ι C D hR a) =
      G.embeddedRimEquiv ι C D hR ((G.rimPairing C).twin a) :=
  Subtype.ext (G.rowEmbeddingPorts_twin ι a.val)

variable (hu : ∀ x ∈ u, x ∉ Set.range C.edge) (hv : ∀ x ∈ v, x ∉ Set.range C.edge)

theorem embeddedRimEquiv_switch (a : G.RimDart C) :
    (G.embedRows ι).rimSwitch D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a) =
        G.embeddedRimEquiv ι C D hR (G.rimSwitch C hu hv a) := by
  apply Eq.symm
  apply (G.embedRows ι).rimSwitch_unique
  · exact (G.rowEmbeddingPorts_vertex_iff ι _ _).mpr (G.rimSwitch_vertex C hu hv a)
  · intro he
    exact G.rimSwitch_ne_self C hu hv a ((G.embeddedRimEquiv ι C D hR).injective he)

theorem embeddedRimEquiv_walk (a : G.RimDart C) :
    (G.embedRows ι).rimWalk D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a) =
        G.embeddedRimEquiv ι C D hR (G.rimWalk C hu hv a) := by
  change (G.embedRows ι).rimSwitch D (embeddedRim_no_boundary ι C D hR hu)
    (embeddedRim_no_boundary ι C D hR hv)
    (((G.embedRows ι).rimPairing D).twin (G.embeddedRimEquiv ι C D hR a)) = _
  rw [G.embeddedRimEquiv_twin ι C D hR, G.embeddedRimEquiv_switch ι C D hR hu hv]
  rfl

theorem embeddedRim_length (a : G.RimDart C) :
    (G.rimSimpleCircuit C hu hv a).length =
      ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
        (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).length :=
  OrbitEnumeration.length_congr _ _ (G.embeddedRimEquiv ι C D hR)
    (G.embeddedRimEquiv_walk ι C D hR hu hv) a

noncomputable def embeddedRimIndex (a : G.RimDart C) :
    Fin (G.rimSimpleCircuit C hu hv a).length ≃
      Fin ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
        (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).length :=
  finCongr (G.embeddedRim_length ι C D hR hu hv a)

theorem embeddedRim_dart (a : G.RimDart C) (i : Fin (G.rimSimpleCircuit C hu hv a).length) :
    ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).dart
        (G.embeddedRimIndex ι C D hR hu hv a i) = G.rowEmbeddingPorts ι ((G.rimSimpleCircuit C hu hv a).dart i) :=
  congrArg Subtype.val (OrbitEnumeration.dart_congr _ _ (G.embeddedRimEquiv ι C D hR)
    (G.embeddedRimEquiv_walk ι C D hR hu hv) a i)

theorem embeddedRim_port (a : G.RimDart C) (i : Fin (G.rimSimpleCircuit C hu hv a).length) (s : Bool) :
    ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).port
        (G.embeddedRimIndex ι C D hR hu hv a i, s) =
          G.rowEmbeddingPorts ι ((G.rimSimpleCircuit C hu hv a).port (i, s)) := by
  cases s
  · exact G.embeddedRim_dart ι C D hR hu hv a i
  · have hi {m n : Nat} (he : m = n) (j : Fin m) :
        (finRotate n).symm (finCongr he j) = finCongr he ((finRotate m).symm j) := by subst n; rfl
    change (G.embedRows ι).pairing.twin ((G.embedRows ι).rimSimpleCircuit D _ _ _ |>.dart
      ((finRotate _).symm (finCongr (G.embeddedRim_length ι C D hR hu hv a) i))) = _
    rw [hi]
    change (G.embedRows ι).pairing.twin ((G.embedRows ι).rimSimpleCircuit D _ _ _ |>.dart
      (G.embeddedRimIndex ι C D hR hu hv a ((finRotate _).symm i))) = _
    rw [G.embeddedRim_dart, G.rowEmbeddingPorts_twin]
    rfl

theorem embeddedRim_boundsFaceOrbit (a : G.RimDart C) (s : Bool)
    (hf : (G.rimSimpleCircuit C hu hv a).BoundsFaceOrbit s) :
    ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).BoundsFaceOrbit s := by
  let L := G.rimSimpleCircuit C hu hv a
  let K := (G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
    (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)
  let e := G.rowEmbeddingPorts ι
  have hp (i : Fin L.length) := G.embeddedRim_port ι C D hR hu hv a i s
  have h0 : K.port (0, s) = e (L.port (0, s)) := hp 0
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  change (G.embedRows ι).circuitStep.SameCycle (e x) (K.port (0, s)) ↔ ∃ i, K.port (i, s) = e x
  rw [h0, ← FiniteReturn.sameCycle_congr G.circuitStep (G.embedRows ι).circuitStep e
    (G.rowEmbeddingPorts_circuitStep ι), hf]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨G.embeddedRimIndex ι C D hR hu hv a i, (hp i).trans (congrArg e hi)⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, rfl⟩ := (G.embeddedRimIndex ι C D hR hu hv a).surjective j
    exact ⟨i, e.injective ((hp i).symm.trans hj)⟩

theorem embeddedRim_isLabelCover (a : G.RimDart C)
    (hc : (G.rimSimpleCircuit C hu hv a).IsLabelCover) :
    ((G.embedRows ι).rimSimpleCircuit D (embeddedRim_no_boundary ι C D hR hu)
      (embeddedRim_no_boundary ι C D hR hv) (G.embeddedRimEquiv ι C D hR a)).IsLabelCover := by
  intro j
  obtain ⟨i, rfl⟩ := (G.embeddedRimIndex ι C D hR hu hv a).surjective j
  obtain ⟨h, k, p, q, hi, ht, hn, hl⟩ := hc i
  have hd := G.embeddedRim_dart ι C D hR hu hv a i
  refine ⟨h, k, ι.slotEquiv (G.hubLabel h) p, ι.slotEquiv (G.hubLabel k) q,
    hd.trans (congrArg (G.rowEmbeddingPorts ι) hi), ?_, hn, fun he => hl (ι.vertex.injective he)⟩
  exact (congrArg (G.embedRows ι).pairing.twin hd).trans
    ((G.rowEmbeddingPorts_twin ι _).trans (congrArg (G.rowEmbeddingPorts ι) ht))

end ThomGame.Pictures.PortGraph
