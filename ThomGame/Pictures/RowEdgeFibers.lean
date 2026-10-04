module

public import ThomGame.Pictures.CircuitCoverEdges
public import ThomGame.Pictures.CycleIntersectionTurns

/-!
# A covered edge pairs the actual fibers over its two endpoint rows

Every hub over an endpoint has a unique port with the selected edge
label. The original edge involution pairs it with a hub over the other
endpoint. Thus it gives an actual equivalence of hub fibers, with an
explicit equation for its paired ports, not only equality of cardinalities.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]

abbrev LabelHub (r : R) := {h : G.Hub // G.hubLabel h = r}

noncomputable def rowEdgeSlot (r : R) (e : S) (he : e ∈ A.hypergraph.incidence r) : Fin 3 :=
  ((A.mem_hypergraph_incidence r e).mp he).choose

omit [DecidableEq R] [DecidableEq S] in
theorem rowEdgeSlot_label (r : R) (e : S) (he : e ∈ A.hypergraph.incidence r) :
    A.column r (rowEdgeSlot r e he) = e :=
  ((A.mem_hypergraph_incidence r e).mp he).choose_spec

noncomputable def rowLabelPort (r : R) (e : S) (he : e ∈ A.hypergraph.incidence r) :
    G.LabelHub r ↪ G.Dart where
  toFun h := .hub h.val (rowEdgeSlot r e he)
  inj' h k hk := by
    apply Subtype.ext
    exact Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex hk))

omit [DecidableEq R] [DecidableEq S] [IsEmpty G.Joint] in
theorem rowLabelPort_vertex (r : R) (e : S) (he : e ∈ A.hypergraph.incidence r) (h : G.LabelHub r) :
    (G.rowLabelPort r e he h).vertex = .inr (.inl h.val) := rfl

omit [DecidableEq R] [DecidableEq S] [IsEmpty G.Joint] in
theorem rowLabelPort_label (r : R) (e : S) (he : e ∈ A.hypergraph.incidence r) (h : G.LabelHub r) :
    Port.label G.jointLabel (G.rowLabelPort r e he h) = e := by
  rw [show G.rowLabelPort r e he h = .hub h.val (rowEdgeSlot r e he) from rfl,
    SolutionGroup.rowGraph_port_label, h.property, rowEdgeSlot_label]

variable {G}

omit [DecidableEq R] [DecidableEq S] in
theorem exists_paired_rowLabelPort (r t : R) (e : S)
    (hr : e ∈ A.hypergraph.incidence r) (ht : e ∈ A.hypergraph.incidence t)
    (hends : ∀ v, e ∈ A.hypergraph.incidence v → v = r ∨ v = t)
    (hc : ∀ x : G.Dart, Port.label G.jointLabel x = e → G.EdgeHasDistinctHubLabels x)
    (h : G.LabelHub r) : ∃ k : G.LabelHub t,
      G.pairing.twin (G.rowLabelPort r e hr h) = G.rowLabelPort t e ht k := by
  obtain ⟨h', k, p, q, hp, hq, _, hne⟩ := hc _ (G.rowLabelPort_label r e hr h)
  have hh : h.val = h' := Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex hp))
  have hl : G.hubLabel h' = r := hh ▸ h.property
  have hlabel : A.column (G.hubLabel k) q = e := by
    rw [← SolutionGroup.rowGraph_port_label A G k q, ← hq,
      G.pairing.label_twin, G.rowLabelPort_label]
  have hk : G.hubLabel k = t :=
    (hends _ ((A.mem_hypergraph_incidence _ _).mpr ⟨q, hlabel⟩)).resolve_left
      (fun he => hne (hl.trans he.symm))
  refine ⟨⟨k, hk⟩, G.row_label_injective_at_vertex ?_ ?_⟩
  · exact (congrArg Port.vertex hq).trans (G.rowLabelPort_vertex t e ht ⟨k, hk⟩).symm
  · exact (G.pairing.label_twin _).trans ((G.rowLabelPort_label r e hr h).trans
      (G.rowLabelPort_label t e ht ⟨k, hk⟩).symm)

noncomputable def rowEdgeHubEquiv (r t : R) (e : S)
    (hr : e ∈ A.hypergraph.incidence r) (ht : e ∈ A.hypergraph.incidence t)
    (hends : ∀ v, e ∈ A.hypergraph.incidence v → v = r ∨ v = t)
    (hc : ∀ x : G.Dart, Port.label G.jointLabel x = e → G.EdgeHasDistinctHubLabels x) :
    G.LabelHub r ≃ G.LabelHub t := by
  let f (h : G.LabelHub r) : G.LabelHub t := (exists_paired_rowLabelPort r t e hr ht hends hc h).choose
  have hf (h : G.LabelHub r) : G.pairing.twin (G.rowLabelPort r e hr h) = G.rowLabelPort t e ht (f h) :=
    (exists_paired_rowLabelPort r t e hr ht hends hc h).choose_spec
  exact Equiv.ofBijective f ⟨by
    intro h k he
    apply (G.rowLabelPort r e hr).injective
    apply G.pairing.perm.injective
    exact (hf h).trans ((congrArg (G.rowLabelPort t e ht) he).trans (hf k).symm), by
    intro k
    obtain ⟨h, hh⟩ := exists_paired_rowLabelPort t r e ht hr (fun v hv => (hends v hv).symm) hc k
    refine ⟨h, (G.rowLabelPort t e ht).injective ?_⟩
    exact (hf h).symm.trans
      ((congrArg G.pairing.twin hh).symm.trans (G.pairing.involutive _))⟩

omit [DecidableEq R] [DecidableEq S] in
theorem rowEdgeHubEquiv_pairing (r t : R) (e : S)
    (hr : e ∈ A.hypergraph.incidence r) (ht : e ∈ A.hypergraph.incidence t)
    (hends : ∀ v, e ∈ A.hypergraph.incidence v → v = r ∨ v = t)
    (hc : ∀ x : G.Dart, Port.label G.jointLabel x = e → G.EdgeHasDistinctHubLabels x)
    (h : G.LabelHub r) :
    G.pairing.twin (G.rowLabelPort r e hr h) =
      G.rowLabelPort t e ht (rowEdgeHubEquiv r t e hr ht hends hc h) :=
  (exists_paired_rowLabelPort r t e hr ht hends hc h).choose_spec

omit [DecidableEq R] [DecidableEq S] in
theorem rowEdgeHubEquiv_edge (r t : R) (e : S)
    (hr : e ∈ A.hypergraph.incidence r) (ht : e ∈ A.hypergraph.incidence t)
    (hends : ∀ v, e ∈ A.hypergraph.incidence v → v = r ∨ v = t)
    (hc : ∀ x : G.Dart, Port.label G.jointLabel x = e → G.EdgeHasDistinctHubLabels x)
    (h : G.LabelHub r) :
    ∃ x : G.Dart, x.vertex = .inr (.inl h.val) ∧
      (G.pairing.twin x).vertex = .inr (.inl (rowEdgeHubEquiv r t e hr ht hends hc h).val) ∧
      Port.label G.jointLabel x = e :=
  ⟨G.rowLabelPort r e hr h, G.rowLabelPort_vertex _ _ _ _,
    (congrArg Port.vertex (rowEdgeHubEquiv_pairing r t e hr ht hends hc h)).trans
      (G.rowLabelPort_vertex _ _ _ _), G.rowLabelPort_label _ _ _ _⟩

omit [DecidableEq R] [DecidableEq S] in
theorem rowEdgeHubEquiv_eq_of_edge (r t : R) (e : S)
    (hr : e ∈ A.hypergraph.incidence r) (ht : e ∈ A.hypergraph.incidence t)
    (hends : ∀ v, e ∈ A.hypergraph.incidence v → v = r ∨ v = t)
    (hc : ∀ x : G.Dart, Port.label G.jointLabel x = e → G.EdgeHasDistinctHubLabels x)
    (h : G.LabelHub r) (k : G.LabelHub t) (x : G.Dart)
    (hx : x.vertex = .inr (.inl h.val)) (hk : (G.pairing.twin x).vertex = .inr (.inl k.val))
    (he : Port.label G.jointLabel x = e) : rowEdgeHubEquiv r t e hr ht hends hc h = k := by
  obtain ⟨y, hy, hyt, hye⟩ := rowEdgeHubEquiv_edge r t e hr ht hends hc h
  have hxy : x = y := G.row_label_injective_at_vertex (hx.trans hy.symm) (he.trans hye.symm)
  apply Subtype.ext
  exact Sum.inl.inj (Sum.inr.inj
    (hyt.symm.trans ((congrArg (fun z : G.Dart => (G.pairing.twin z).vertex) hxy).symm.trans hk)))

variable (C : Hypergraph.Cycle A.hypergraph) (i : Fin C.length)
  (hc : ∀ x : G.Dart, Port.label G.jointLabel x = C.edge i → G.EdgeHasDistinctHubLabels x)

noncomputable def cycleEdgeHubEquiv :
    G.LabelHub (C.vertex ((finRotate C.length).symm i)) ≃ G.LabelHub (C.vertex i) :=
  rowEdgeHubEquiv _ _ (C.edge i)
    ((C.incident_iff _ i).mpr (Or.inr rfl)) ((C.incident_iff _ i).mpr (Or.inl rfl))
    (fun v hv => ((C.incident_iff v i).mp hv).symm) hc

theorem cycleEdgeHubEquiv_edge (h : G.LabelHub (C.vertex ((finRotate C.length).symm i))) :
    ∃ x : G.Dart, x.vertex = .inr (.inl h.val) ∧
      (G.pairing.twin x).vertex = .inr (.inl (cycleEdgeHubEquiv C i hc h).val) ∧
      Port.label G.jointLabel x = C.edge i := by
  let hr := (C.incident_iff _ i).mpr (Or.inr rfl)
  let ht := (C.incident_iff _ i).mpr (Or.inl rfl)
  refine ⟨G.rowLabelPort _ (C.edge i) hr h, G.rowLabelPort_vertex _ _ _ _, ?_,
    G.rowLabelPort_label _ _ _ _⟩
  exact (congrArg Port.vertex (rowEdgeHubEquiv_pairing _ _ (C.edge i) hr ht
    (fun v hv => ((C.incident_iff v i).mp hv).symm) hc h)).trans (G.rowLabelPort_vertex _ _ _ _)

theorem cycleEdgeHubEquiv_eq_iff
    (h : G.LabelHub (C.vertex ((finRotate C.length).symm i))) (k : G.LabelHub (C.vertex i)) :
    cycleEdgeHubEquiv C i hc h = k ↔ ∃ x : G.Dart,
      x.vertex = .inr (.inl h.val) ∧ (G.pairing.twin x).vertex = .inr (.inl k.val) ∧
        Port.label G.jointLabel x = C.edge i := by
  constructor
  · rintro rfl
    exact cycleEdgeHubEquiv_edge C i hc h
  · rintro ⟨x, hx, hk, he⟩
    obtain ⟨y, hy, hyt, hye⟩ := cycleEdgeHubEquiv_edge C i hc h
    have hxy : x = y := G.row_label_injective_at_vertex (hx.trans hy.symm) (he.trans hye.symm)
    apply Subtype.ext
    exact Sum.inl.inj (Sum.inr.inj
      (hyt.symm.trans ((congrArg (fun z : G.Dart => (G.pairing.twin z).vertex) hxy).symm.trans hk)))

end ThomGame.Pictures.PortGraph
