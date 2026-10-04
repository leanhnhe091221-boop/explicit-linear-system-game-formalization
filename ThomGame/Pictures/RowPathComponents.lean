module

public import ThomGame.Pictures.RowPathCovers
public import ThomGame.Pictures.CircuitGermThreeSteps

/-!
# Every connected component of a covered path is one actual copy

The hub equivalence from path lifting respects exactly the original
selected-edge adjacency: adjacent vertices have the same starting hub
and consecutive path positions. Actual restricted connectivity is
therefore equality of starting hubs, so no longer or folded component
is hidden in the covering hypothesis.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]

omit [DecidableEq R] [DecidableEq S] in
theorem row_port_incident (x : G.Dart) (h : G.Hub) (hx : x.vertex = .inr (.inl h)) :
    Port.label G.jointLabel x ∈ A.hypergraph.incidence (G.hubLabel h) := by
  obtain ⟨k, p, rfl⟩ := exists_hub_dart x
  have hk : k = h := Sum.inl.inj (Sum.inr.inj hx)
  subst k
  exact (A.mem_hypergraph_incidence _ _).mpr
    ⟨p, (SolutionGroup.rowGraph_port_label A G h p).symm⟩

omit [DecidableEq R] [DecidableEq S] [IsEmpty G.Joint] in
theorem edgeHasDistinctHubLabels_ne {x : G.Dart} (hc : G.EdgeHasDistinctHubLabels x)
    (h k : G.Hub) (hx : x.vertex = .inr (.inl h))
    (hy : (G.pairing.twin x).vertex = .inr (.inl k)) : G.hubLabel h ≠ G.hubLabel k := by
  obtain ⟨h', k', p, q, hp, hq, _, hne⟩ := hc
  have hh : h' = h := Sum.inl.inj (Sum.inr.inj ((congrArg Port.vertex hp).symm.trans hx))
  have hk : k' = k := Sum.inl.inj (Sum.inr.inj ((congrArg Port.vertex hq).symm.trans hy))
  exact hh ▸ hk ▸ hne

namespace RowPath

variable (P : RowPath A)
  (hc : ∀ x : G.Dart, Port.label G.jointLabel x ∈ Set.range P.edge → G.EdgeHasDistinctHubLabels x)

abbrev Node := {h : G.Hub // G.hubLabel h ∈ Set.range P.vertex}

def Adj (v w : P.Node G) : Prop := ∃ x : G.Dart,
  Port.label G.jointLabel x ∈ Set.range P.edge ∧
    x.vertex = .inr (.inl v.val) ∧ (G.pairing.twin x).vertex = .inr (.inl w.val)

def Connected : P.Node G → P.Node G → Prop := Relation.EqvGen (P.Adj G)

omit [DecidableEq R] [DecidableEq S] [IsEmpty G.Joint] in
theorem adj_symm {v w : P.Node G} (h : P.Adj G v w) : P.Adj G w v := by
  obtain ⟨x, he, hx, hy⟩ := h
  exact ⟨G.pairing.twin x, (G.pairing.label_twin x).symm ▸ he, hy,
    (congrArg Port.vertex (G.pairing.involutive x)).trans hx⟩

omit [DecidableEq R] [DecidableEq S] in
theorem adj_lift_iff (h k : G.LabelHub (P.vertex 0)) (i l : Fin (P.length + 1)) :
    P.Adj G (P.hubEquiv G hc (h, i)) (P.hubEquiv G hc (k, l)) ↔
      h = k ∧ ∃ j : Fin P.length,
        (i = j.castSucc ∧ l = j.succ) ∨ (i = j.succ ∧ l = j.castSucc) := by
  constructor
  · rintro ⟨x, ⟨j, hj⟩, hx, hy⟩
    have hL := G.row_port_incident x (P.hub G hc h i) hx
    have hR := G.row_port_incident (G.pairing.twin x) (P.hub G hc k l) hy
    rw [← hj, P.hub_label] at hL
    rw [G.pairing.label_twin, ← hj, P.hub_label] at hR
    have hi : i = j.castSucc ∨ i = j.succ :=
      ((P.incident _ j).mp hL).imp (fun he => P.vertex.injective he) (fun he => P.vertex.injective he)
    have hl : l = j.castSucc ∨ l = j.succ :=
      ((P.incident _ j).mp hR).imp (fun he => P.vertex.injective he) (fun he => P.vertex.injective he)
    have hne := G.edgeHasDistinctHubLabels_ne (hc x ⟨j, hj⟩)
      (P.hub G hc h i) (P.hub G hc k l) hx hy
    rw [P.hub_label, P.hub_label] at hne
    rcases hi with rfl | rfl <;> rcases hl with rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨P.seed_eq_of_edge G hc h k j x hx hy hj.symm, j, Or.inl ⟨rfl, rfl⟩⟩
    · have he := P.seed_eq_of_edge G hc k h j (G.pairing.twin x) hy
        ((congrArg Port.vertex (G.pairing.involutive x)).trans hx)
        ((G.pairing.label_twin x).trans hj.symm)
      exact ⟨he.symm, j, Or.inr ⟨rfl, rfl⟩⟩
    · exact (hne rfl).elim
  · rintro ⟨rfl, j, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · obtain ⟨x, hx, hy, he⟩ := P.lift_edge G hc h j
      exact ⟨x, ⟨j, he.symm⟩, hx, hy⟩
    · apply P.adj_symm G
      obtain ⟨x, hx, hy, he⟩ := P.lift_edge G hc h j
      exact ⟨x, ⟨j, he.symm⟩, hx, hy⟩

omit [DecidableEq R] [DecidableEq S] in
theorem connected_lift_zero (h : G.LabelHub (P.vertex 0)) (i : Fin (P.length + 1)) :
    P.Connected G (P.hubEquiv G hc (h, 0)) (P.hubEquiv G hc (h, i)) := by
  induction i using Fin.induction with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _
      ((P.adj_lift_iff G hc h h j.castSucc j.succ).mpr ⟨rfl, j, Or.inl ⟨rfl, rfl⟩⟩))

omit [DecidableEq R] [DecidableEq S] in
theorem connected_iff_seed (v w : P.Node G) :
    P.Connected G v w ↔ ((P.hubEquiv G hc).symm v).1 = ((P.hubEquiv G hc).symm w).1 := by
  constructor
  · intro h
    induction h with
    | rel v w ha =>
      obtain ⟨⟨h, i⟩, rfl⟩ := (P.hubEquiv G hc).surjective v
      obtain ⟨⟨k, j⟩, rfl⟩ := (P.hubEquiv G hc).surjective w
      simpa only [Equiv.symm_apply_apply] using ((P.adj_lift_iff G hc h k i j).mp ha).1
    | refl v => rfl
    | symm v w _ ih => exact ih.symm
    | trans v w z _ _ ih ik => exact ih.trans ik
  · obtain ⟨⟨h, i⟩, rfl⟩ := (P.hubEquiv G hc).surjective v
    obtain ⟨⟨k, j⟩, rfl⟩ := (P.hubEquiv G hc).surjective w
    simp only [Equiv.symm_apply_apply]
    intro hhk
    subst k
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (P.connected_lift_zero G hc h i))
      (P.connected_lift_zero G hc h j)

noncomputable def componentEquiv (h : G.LabelHub (P.vertex 0)) :
    Fin (P.length + 1) ≃ {v : P.Node G // P.Connected G (P.hubEquiv G hc (h, 0)) v} :=
  Equiv.ofBijective (fun i => ⟨P.hubEquiv G hc (h, i), P.connected_lift_zero G hc h i⟩)
    ⟨by
      intro i j he
      exact (Prod.mk.inj ((P.hubEquiv G hc).injective (congrArg Subtype.val he))).2, by
      rintro ⟨v, hv⟩
      obtain ⟨⟨k, i⟩, rfl⟩ := (P.hubEquiv G hc).surjective v
      have hh : h = k := by
        simpa only [Equiv.symm_apply_apply] using (P.connected_iff_seed G hc _ _).mp hv
      subst k
      exact ⟨i, rfl⟩⟩

omit [DecidableEq R] [DecidableEq S] in
theorem component_card (h : G.LabelHub (P.vertex 0)) :
    Nat.card {v : P.Node G // P.Connected G (P.hubEquiv G hc (h, 0)) v} = P.length + 1 := by
  rw [← Nat.card_congr (P.componentEquiv G hc h), Nat.card_fin]

end RowPath
end ThomGame.Pictures.PortGraph
