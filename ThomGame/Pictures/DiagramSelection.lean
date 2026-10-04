module

public import ThomGame.Pictures.GraphSelection

/-!
# Extracting selected components as actual diagrams

Deleting complete components can be performed recursively in the planar
diagram syntax. The result retains exactly the selected relation occurrences,
in their original syntax order. No arbitrary disk-region realization is used.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph.Selection

theorem identity_boundary {w : List S} (c : (PortGraph.identity P w).Selection) :
    c.bottom = c.top := by
  funext i
  exact c.edge (.top i)

theorem cap_boundary {s : S} (c : (PortGraph.cap P s).Selection) (i : Fin 2) :
    c.top i = c.top 0 := by
  fin_cases i
  · rfl
  · exact c.edge (.top 0)

theorem cup_boundary {s : S} (c : (PortGraph.cup P s).Selection) (i : Fin 2) :
    c.bottom i = c.bottom 0 := by
  fin_cases i
  · rfl
  · exact c.edge (.bottom 0)

theorem down_boundary {r : R} (c : (PortGraph.down P r).Selection)
    (i : Fin (P.word r).length) : c.top i = c.hub () := (c.edge (.top i)).symm

theorem up_boundary {r : R} (c : (PortGraph.up P r).Selection)
    (i : Fin (P.word r).length) : c.bottom i = c.hub () := (c.edge (.bottom i)).symm

end PortGraph.Selection

namespace Diagram

variable {u v : List S}

/-- The subsequence of relation occurrences selected on actual graph hubs. -/
def selectedLabels : {u v : List S} → (d : Diagram P u v) → (d.graph.Hub → Bool) → List R
  | _, _, .identity _, _ => []
  | _, _, .cap _, _ => []
  | _, _, .cup _, _ => []
  | _, _, .down r, b => if b () then [r] else []
  | _, _, .up r, b => if b () then [r] else []
  | _, _, .comp d e, b => d.selectedLabels (fun h => b (.inl h)) ++
      e.selectedLabels (fun h => b (.inr h))
  | _, _, .tensor d e, b => d.selectedLabels (fun h => b (.inl h)) ++
      e.selectedLabels (fun h => b (.inr h))

theorem selectedLabels_sublist (d : Diagram P u v) (b : d.graph.Hub → Bool) :
    (d.selectedLabels b).Sublist d.labels := by
  induction d with
  | identity w => exact List.Sublist.refl _
  | cap s => exact List.Sublist.refl _
  | cup s => exact List.Sublist.refl _
  | down r => simp only [selectedLabels]; split <;> simp [labels]
  | up r => simp only [selectedLabels]; split <;> simp [labels]
  | comp d e ihd ihe => exact (ihd _).append (ihe _)
  | tensor d e ihd ihe => exact (ihd _).append (ihe _)

theorem sum_selectedLabels {A : Type*} [AddCommMonoid A] (d : Diagram P u v)
    (b : d.graph.Hub → Bool) (weight : R → A) :
    ((d.selectedLabels b).map weight).sum =
      ∑ h : d.graph.Hub, if b h then weight (d.graph.hubLabel h) else 0 := by
  induction d with
  | identity w =>
    change 0 = ∑ h : Empty, if b h then weight h.elim else 0
    exact Finset.sum_empty.symm
  | cap s =>
    change 0 = ∑ h : Empty, if b h then weight h.elim else 0
    exact Finset.sum_empty.symm
  | cup s =>
    change 0 = ∑ h : Empty, if b h then weight h.elim else 0
    exact Finset.sum_empty.symm
  | down r =>
    change Unit → Bool at b
    change ((if b () then [r] else []).map weight).sum =
      ∑ h : Unit, if b h then weight r else 0
    cases h : b () <;> simp [h]
  | up r =>
    change Unit → Bool at b
    change ((if b () then [r] else []).map weight).sum =
      ∑ h : Unit, if b h then weight r else 0
    cases h : b () <;> simp [h]
  | comp d e ihd ihe =>
    change ((d.selectedLabels _ ++ e.selectedLabels _).map weight).sum =
      ∑ h : d.graph.Hub ⊕ e.graph.Hub, if b h then
        weight (Sum.elim d.graph.hubLabel e.graph.hubLabel h) else 0
    rw [List.map_append, List.sum_append, ihd, ihe, Fintype.sum_sum_type]
    rfl
  | tensor d e ihd ihe =>
    change ((d.selectedLabels _ ++ e.selectedLabels _).map weight).sum =
      ∑ h : d.graph.Hub ⊕ e.graph.Hub, if b h then
        weight (Sum.elim d.graph.hubLabel e.graph.hubLabel h) else 0
    rw [List.map_append, List.sum_append, ihd, ihe, Fintype.sum_sum_type]
    rfl

/-- Whole-component deletion has an actual witness in the diagram syntax. -/
theorem exists_selected (d : Diagram P u v) (c : d.graph.Selection) :
    ∃ e : Diagram P (selectPositions u c.top) (selectPositions v c.bottom),
      e.labels = d.selectedLabels c.hub := by
  induction d with
  | identity w =>
    change (PortGraph.identity P w).Selection at c
    refine ⟨(identity (selectPositions w c.top)).cast rfl
      (congrArg (selectPositions w) c.identity_boundary.symm), ?_⟩
    exact labels_cast _ _ _
  | cap s =>
    change (PortGraph.cap P s).Selection at c
    change ∃ e : Diagram P (selectPositions [s, s] c.top) [], e.labels = []
    have hc : selectPositions [s, s] c.top = if c.top 0 then [s, s] else [] :=
      (selectPositions_congr [s, s] c.cap_boundary).trans (selectPositions_const _ _)
    cases h : c.top 0
    · refine ⟨(identity []).cast (by simpa [h] using hc.symm) rfl, ?_⟩
      exact labels_cast _ _ _
    · refine ⟨(cap s).cast (by simpa [h] using hc.symm) rfl, ?_⟩
      exact labels_cast _ _ _
  | cup s =>
    change (PortGraph.cup P s).Selection at c
    change ∃ e : Diagram P [] (selectPositions [s, s] c.bottom), e.labels = []
    have hc : selectPositions [s, s] c.bottom = if c.bottom 0 then [s, s] else [] :=
      (selectPositions_congr [s, s] c.cup_boundary).trans (selectPositions_const _ _)
    cases h : c.bottom 0
    · refine ⟨(identity []).cast rfl (by simpa [h] using hc.symm), ?_⟩
      exact labels_cast _ _ _
    · refine ⟨(cup s).cast rfl (by simpa [h] using hc.symm), ?_⟩
      exact labels_cast _ _ _
  | down r =>
    change (PortGraph.down P r).Selection at c
    change ∃ e : Diagram P (selectPositions (P.word r) c.top) [],
      e.labels = if c.hub () then [r] else []
    have hc : selectPositions (P.word r) c.top = if c.hub () then P.word r else [] :=
      (selectPositions_congr (P.word r) c.down_boundary).trans (selectPositions_const _ _)
    cases h : c.hub ()
    · refine ⟨(identity []).cast (by simpa [h] using hc.symm) rfl, ?_⟩
      exact (labels_cast _ _ _).trans (by simp [labels])
    · refine ⟨(down r).cast (by simpa [h] using hc.symm) rfl, ?_⟩
      exact (labels_cast _ _ _).trans (by simp [labels])
  | up r =>
    change (PortGraph.up P r).Selection at c
    change ∃ e : Diagram P [] (selectPositions (P.word r) c.bottom),
      e.labels = if c.hub () then [r] else []
    have hc : selectPositions (P.word r) c.bottom = if c.hub () then P.word r else [] :=
      (selectPositions_congr (P.word r) c.up_boundary).trans (selectPositions_const _ _)
    cases h : c.hub ()
    · refine ⟨(identity []).cast rfl (by simpa [h] using hc.symm), ?_⟩
      exact (labels_cast _ _ _).trans (by simp [labels])
    · refine ⟨(up r).cast rfl (by simpa [h] using hc.symm), ?_⟩
      exact (labels_cast _ _ _).trans (by simp [labels])
  | comp d e ihd ihe =>
    change (d.graph.comp e.graph).Selection at c
    obtain ⟨d', hd⟩ := ihd c.compLeft
    obtain ⟨e', he⟩ := ihe c.compRight
    exact ⟨d'.comp e', congrArg₂ List.append hd he⟩
  | @tensor u v w z d e ihd ihe =>
    change (d.graph.tensor e.graph).Selection at c
    obtain ⟨d', hd⟩ := ihd c.tensorLeft
    obtain ⟨e', he⟩ := ihe c.tensorRight
    refine ⟨(d'.tensor e').cast (selectPositions_append u w c.top).symm
      (selectPositions_append v z c.bottom).symm, ?_⟩
    exact (labels_cast _ _ _).trans (congrArg₂ List.append hd he)

noncomputable def select (d : Diagram P u v) (c : d.graph.Selection) :
    Diagram P (selectPositions u c.top) (selectPositions v c.bottom) :=
  Classical.choose (d.exists_selected c)

theorem labels_select (d : Diagram P u v) (c : d.graph.Selection) :
    (d.select c).labels = d.selectedLabels c.hub := Classical.choose_spec (d.exists_selected c)

theorem size_select_le (d : Diagram P u v) (c : d.graph.Selection) :
    (d.select c).size ≤ d.size := by
  unfold size
  rw [labels_select]
  exact (d.selectedLabels_sublist c.hub).length_le

theorem sum_labels_select {A : Type*} [AddCommMonoid A] (d : Diagram P u v)
    (c : d.graph.Selection) (weight : R → A) :
    ((d.select c).labels.map weight).sum =
      ∑ h : d.graph.Hub, if c.hub h then weight (d.graph.hubLabel h) else 0 := by
  rw [labels_select, sum_selectedLabels]

theorem sign_select (d : Diagram P u v) (c : d.graph.Selection) :
    (d.select c).sign =
      ∑ h : d.graph.Hub, if c.hub h then P.parity (d.graph.hubLabel h) else 0 :=
  d.sum_labels_select c P.parity

theorem size_select (d : Diagram P u v) (c : d.graph.Selection) :
    (d.select c).size = ∑ h : d.graph.Hub, if c.hub h then 1 else 0 := by
  simpa [size] using d.sum_labels_select c (fun _ => (1 : Nat))

end Diagram
end ThomGame.Pictures
