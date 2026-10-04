module

public import ThomGame.Pictures.FrameComplement

/-!
# Puncturing the unique occurrence of an added relation

An auxiliary relation with prescribed word can cap an outer boundary.
If it occurs exactly once in a closed diagram, removing that occurrence
gives an actual diagram over the original presentation, with that exact
boundary word and all ordinary relation occurrences preserved.
-/

@[expose] public section
namespace ThomGame

variable {R S : Type*}

def InvolutionPresentation.adjoinRelation (P : InvolutionPresentation R S)
    (w : List S) (p : ZMod 2) : InvolutionPresentation (Option R) S where
  word r := r.elim w P.word
  parity r := r.elim p P.parity

namespace Pictures.Diagram

open scoped Classical

variable {P : InvolutionPresentation R S} {w : List S} {p : ZMod 2}
    {u v : List S}

def adjoinRelation (w : List S) (p : ZMod 2) :
    {u v : List S} → Diagram P u v → Diagram (P.adjoinRelation w p) u v
  | _, _, .identity u => .identity u
  | _, _, .cap s => .cap s
  | _, _, .cup s => .cup s
  | _, _, .down r => .down (some r)
  | _, _, .up r => .up (some r)
  | _, _, .comp d e => (d.adjoinRelation w p).comp (e.adjoinRelation w p)
  | _, _, .tensor d e => (d.adjoinRelation w p).tensor (e.adjoinRelation w p)

theorem labels_adjoinRelation (d : Diagram P u v) (w : List S) (p : ZMod 2) :
    (d.adjoinRelation w p).labels = d.labels.map some := by
  induction d <;> simp [adjoinRelation, labels, *]

theorem exists_erase_absent_relation
    (d : Diagram (P.adjoinRelation w p) u v) :
    none ∉ d.labels → ∃ e : Diagram P u v, e.labels = d.labels.filterMap id := by
  induction d with
  | identity u => intro _; exact ⟨.identity u, rfl⟩
  | cap s => intro _; exact ⟨.cap s, rfl⟩
  | cup s => intro _; exact ⟨.cup s, rfl⟩
  | down r =>
    intro h
    cases r with
    | none => exact (h (by simp [labels])).elim
    | some r => exact ⟨.down r, rfl⟩
  | up r =>
    intro h
    cases r with
    | none => exact (h (by simp [labels])).elim
    | some r => exact ⟨.up r, rfl⟩
  | comp d e ihd ihe =>
    intro h
    have hh : none ∉ d.labels ∧ none ∉ e.labels := by
      simpa only [labels, List.mem_append, not_or] using h
    obtain ⟨d', hd'⟩ := ihd hh.1
    obtain ⟨e', he'⟩ := ihe hh.2
    exact ⟨d'.comp e', by simp only [labels, hd', he', List.filterMap_append]⟩
  | tensor d e ihd ihe =>
    intro h
    have hh : none ∉ d.labels ∧ none ∉ e.labels := by
      simpa only [labels, List.mem_append, not_or] using h
    obtain ⟨d', hd'⟩ := ihd hh.1
    obtain ⟨e', he'⟩ := ihe hh.2
    exact ⟨d'.tensor e', by simp only [labels, hd', he', List.filterMap_append]⟩

theorem exists_frame_of_unique_relation
    (d : Diagram (P.adjoinRelation w p) u v) :
    d.labels.count none = 1 →
      (∃ c : Frame P w [] u v, c.labels = d.labels.filterMap id) ∨
      (∃ c : Frame P [] w u v, c.labels = d.labels.filterMap id) := by
  induction d with
  | identity u => simp [labels]
  | cap s => simp [labels]
  | cup s => simp [labels]
  | down r =>
    intro h
    cases r with
    | none => exact Or.inl ⟨.hole, rfl⟩
    | some r => simp [labels] at h
  | up r =>
    intro h
    cases r with
    | none => exact Or.inr ⟨.hole, rfl⟩
    | some r => simp [labels] at h
  | comp d e ihd ihe =>
    intro h
    have hn : d.labels.count none + e.labels.count none = 1 := by
      simpa only [labels, List.count_append] using h
    by_cases hd : d.labels.count none = 0
    · obtain ⟨d', hd'⟩ := d.exists_erase_absent_relation (List.count_eq_zero.mp hd)
      have he : e.labels.count none = 1 := by omega
      rcases ihe he with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨.pre d' c, by
          simp only [Frame.labels, labels, hd', hc, List.filterMap_append]⟩
      · exact Or.inr ⟨.pre d' c, by
          simp only [Frame.labels, labels, hd', hc, List.filterMap_append]⟩
    · have hd1 : d.labels.count none = 1 := by omega
      have he : e.labels.count none = 0 := by omega
      obtain ⟨e', he'⟩ := e.exists_erase_absent_relation (List.count_eq_zero.mp he)
      rcases ihd hd1 with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨.post c e', by
          simp only [Frame.labels, labels, he', hc, List.filterMap_append]⟩
      · exact Or.inr ⟨.post c e', by
          simp only [Frame.labels, labels, he', hc, List.filterMap_append]⟩
  | tensor d e ihd ihe =>
    intro h
    have hn : d.labels.count none + e.labels.count none = 1 := by
      simpa only [labels, List.count_append] using h
    by_cases hd : d.labels.count none = 0
    · obtain ⟨d', hd'⟩ := d.exists_erase_absent_relation (List.count_eq_zero.mp hd)
      have he : e.labels.count none = 1 := by omega
      rcases ihe he with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨.left d' c, by
          simp only [Frame.labels, labels, hd', hc, List.filterMap_append]⟩
      · exact Or.inr ⟨.left d' c, by
          simp only [Frame.labels, labels, hd', hc, List.filterMap_append]⟩
    · have hd1 : d.labels.count none = 1 := by omega
      have he : e.labels.count none = 0 := by omega
      obtain ⟨e', he'⟩ := e.exists_erase_absent_relation (List.count_eq_zero.mp he)
      rcases ihd hd1 with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨.right c e', by
          simp only [Frame.labels, labels, he', hc, List.filterMap_append]⟩
      · exact Or.inr ⟨.right c e', by
          simp only [Frame.labels, labels, he', hc, List.filterMap_append]⟩

theorem exists_punctured_diagram
    (d : Diagram (P.adjoinRelation w p) [] []) (h : d.labels.count none = 1) :
    ∃ e : Diagram P w [], e.labels.Perm (d.labels.filterMap id) := by
  rcases d.exists_frame_of_unique_relation h with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine ⟨c.puncture.adjoint, ?_⟩
    rw [← hc]
    exact c.puncture.labels_adjoint_perm.trans c.labels_puncture
  · refine ⟨c.puncture, ?_⟩
    rw [← hc]
    exact c.labels_puncture

theorem exists_punctured_diagram_of_labels
    (d : Diagram (P.adjoinRelation w p) [] []) (rs : List R)
    (h : d.labels.Perm (none :: rs.map some)) :
    ∃ e : Diagram P w [], e.labels.Perm rs := by
  have hn : d.labels.count none = 1 := by
    rw [h.count_eq none]
    simp [List.count_eq_zero]
  obtain ⟨e, he⟩ := d.exists_punctured_diagram hn
  refine ⟨e, he.trans ?_⟩
  simpa using h.filterMap id

theorem exists_punctured_diagram_of_multiset
    (d : Diagram (P.adjoinRelation w p) [] []) (m : Multiset R)
    (h : (d.labels : Multiset (Option R)) = {none} + m.map some) :
    ∃ e : Diagram P w [], (e.labels : Multiset R) = m := by
  obtain ⟨rs, rfl⟩ := Quotient.exists_rep m
  have hp : d.labels.Perm (none :: rs.map some) := Multiset.coe_eq_coe.mp h
  obtain ⟨e, he⟩ := d.exists_punctured_diagram_of_labels rs hp
  exact ⟨e, Multiset.coe_eq_coe.mpr he⟩

end Pictures.Diagram
end ThomGame
