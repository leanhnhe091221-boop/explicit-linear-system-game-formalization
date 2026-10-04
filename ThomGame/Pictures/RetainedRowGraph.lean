module

public import ThomGame.Pictures.RowRelabellingInvariants

/-!
# Generalized maps on graphs with no deleted relation hubs

The retained-vertex hypothesis yields an actual row relabelling. Every
incident edge survives because both rows are trivalent. For a graph with
no joints and retained boundary, every dart has its prescribed optional
edge image; the arbitrary value used away from the graph is never used
on its ports. The relation multiset is exactly the filtered original one.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

theorem filterMap_card_retained {R T : Type*} (f : R → Option T) (m : Multiset R)
    (hc : (m.filterMap f).card = m.card) {r : R} (hr : r ∈ m) : ∃ t, f r = some t := by
  revert hc hr
  refine Quotient.inductionOn m fun l hc hr => ?_
  cases he : f r with
  | some t => exact ⟨t, rfl⟩
  | none =>
    have hm : r ∈ l := hr
    have hlt := List.length_filterMap_lt_length_iff_exists.mpr ⟨r, hm, he⟩
    exact (Nat.ne_of_lt hlt hc).elim

namespace PortGraph

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} (G : SolutionGroup.RowGraph A u v)

theorem hubs_retained_of_filterMap_card (f : R → Option T)
    (hc : ((∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).filterMap f).card = Fintype.card G.Hub)
    (h : G.Hub) : ∃ t, f (G.hubLabel h) = some t := by
  have hs : (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).card = Fintype.card G.Hub := by simp
  apply filterMap_card_retained f _ (hc.trans hs.symm)
  have hm : ([G.hubLabel h] : Multiset R) ≤ ∑ k : G.Hub, ([G.hubLabel k] : Multiset R) :=
    Finset.single_le_sum (f := fun k : G.Hub => ([G.hubLabel k] : Multiset R))
      (fun _ _ => zero_le) (Finset.mem_univ h)
  exact Multiset.mem_of_le hm (by simp)

namespace RowRelabelling

variable (φ : A.hypergraph.GeneralizedHom B.hypergraph) (fallback : U)
  (hV : ∀ h : G.Hub, ∃ t, φ.vertex (G.hubLabel h) = some t)

noncomputable def ofRetained : G.RowRelabelling B where
  edge e := (φ.edge e).getD fallback
  hub h := Classical.choose (hV h)
  incidence h := φ.retained_map_incidence (Classical.choose_spec (hV h)) fallback

theorem ofRetained_hub (h : G.Hub) :
    φ.vertex (G.hubLabel h) = some ((ofRetained G φ fallback hV).hub h) :=
  Classical.choose_spec (hV h)

theorem ofRetained_hub_relations :
    (∑ h : (ofRetained G φ fallback hV).graph.Hub,
      ([(ofRetained G φ fallback hV).graph.hubLabel h] : Multiset T)) =
        (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).filterMap φ.vertex := by
  let F : Multiset R →+ Multiset T := {
    toFun := Multiset.filterMap φ.vertex
    map_zero' := Multiset.filterMap_zero _
    map_add' := Multiset.filterMap_add _ }
  change (∑ h : G.Hub, ([(ofRetained G φ fallback hV).hub h] : Multiset T)) =
    F (∑ h : G.Hub, ([G.hubLabel h] : Multiset R))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro h _
  change _ = Multiset.filterMap φ.vertex (G.hubLabel h ::ₘ 0)
  rw [Multiset.filterMap_cons_some _ _ _ (ofRetained_hub G φ fallback hV h), Multiset.filterMap_zero]
  rfl

theorem retained_word_map {w : List S} (hw : ∀ e ∈ w, ∃ f, φ.edge e = some f) :
    w.map (ofRetained G φ fallback hV).edge = w.filterMap φ.edge := by
  symm
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro e he
  obtain ⟨f, hf⟩ := hw e he
  change φ.edge e = some ((φ.edge e).getD fallback)
  rw [hf]
  rfl

variable [IsEmpty G.Joint]
  (hu : ∀ e ∈ u, ∃ f, φ.edge e = some f)
  (hv : ∀ e ∈ v, ∃ f, φ.edge e = some f)

include hu hv hV in
theorem retained_dart_edge (a : G.Dart) : ∃ f, φ.edge (Port.label G.jointLabel a) = some f := by
  cases a with
  | top i => exact hu _ (List.getElem_mem i.isLt)
  | bottom i => exact hv _ (List.getElem_mem i.isLt)
  | joint j _ => exact isEmptyElim j
  | hub h i =>
    rw [SolutionGroup.rowGraph_port_label A G h i]
    exact φ.retained_incident_image (Classical.choose_spec (hV h))
      ((A.mem_hypergraph_incidence _ _).mpr ⟨i, rfl⟩)

include hu hv in
theorem ofRetained_port_image (a : G.Dart) :
    φ.edge (Port.label G.jointLabel a) =
      some (Port.label (ofRetained G φ fallback hV).graph.jointLabel
        ((ofRetained G φ fallback hV).ports a)) := by
  rw [(ofRetained G φ fallback hV).ports_label]
  obtain ⟨f, hf⟩ := retained_dart_edge G φ hV hu hv a
  change φ.edge (Port.label G.jointLabel a) = some ((φ.edge (Port.label G.jointLabel a)).getD fallback)
  rw [hf]
  rfl

end RowRelabelling
end PortGraph
end ThomGame.Pictures
