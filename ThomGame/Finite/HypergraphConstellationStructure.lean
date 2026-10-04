module

public import ThomGame.Finite.HypergraphConstellation

/-!
# Structure and restriction of constellations

Slofstra Lemmas 11.5 and 11.6. The bound of two cycles through an edge
uses the actual cubic sun neighbourhood and the intersection condition.
Restriction preserves private edges, or makes the edge shared with an
omitted private neighbour into a new private edge.
-/

@[expose] public section
namespace ThomGame.Hypergraph

variable {V E I : Type*} [DecidableEq V] [DecidableEq E]
  {H : Hypergraph V E} {Φ : I → Cycle H} {b : V → ZMod 2}

theorem HasPrivateEdge.restrict {s : Set I} {i : s} (hi : HasPrivateEdge Φ i.val) :
    HasPrivateEdge (fun j : s => Φ j.val) i := by
  obtain ⟨e, he, hu⟩ := hi
  exact ⟨e, he, fun j hj => Subtype.ext (hu j.val hj)⟩

namespace Constellation

variable (h : Constellation Φ b)

include h in
/-- A second cycle through a rim edge must use the external spoke at
each common endpoint: the other rim edge would give two shared edges. -/
theorem spoke_mem_of_shared {i j : I} (hij : i ≠ j) (a : Fin (Φ i).length)
    (hej : (Φ i).edge a ∈ Set.range (Φ j).edge) :
    (h.neighbourhood i).spoke a ∈ Set.range (Φ j).edge := by
  have hei : (Φ i).edge a ∈ Set.range (Φ i).edge := ⟨a, rfl⟩
  have hev : (Φ i).edge a ∈ H.incidence ((Φ i).vertex a) :=
    ((Φ i).incident_index_iff a a).mpr (Or.inl rfl)
  obtain ⟨f, hfj, hfv, hfe⟩ :=
    (Φ j).exists_other_incident ((Φ j).closed hej hev) ((Φ i).edge a)
  rw [(h.neighbourhood i).incidence_eq a] at hfv
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hfv
  rcases hfv with hs | he | hn
  · exact hs ▸ hfj
  · exact (hfe he).elim
  · have hfi : f ∈ Set.range (Φ i).edge := ⟨finRotate (Φ i).length a, hn.symm⟩
    exact (hfe (h.intersection_unique i j hij _ _ hei hej hfi hfj).symm).elim

include h in
/-- Once two distinct cycles contain an edge, every cycle containing it
is one of those two. This is the multiplicity bound in Lemma 11.5. -/
theorem eq_or_eq_of_mem {i j k : I} (hij : i ≠ j) {e : E}
    (hei : e ∈ Set.range (Φ i).edge) (hej : e ∈ Set.range (Φ j).edge)
    (hek : e ∈ Set.range (Φ k).edge) : k = i ∨ k = j := by
  classical
  by_cases hki : k = i
  · exact Or.inl hki
  by_cases hkj : k = j
  · exact Or.inr hkj
  obtain ⟨a, rfl⟩ := hei
  have hsj := h.spoke_mem_of_shared hij a hej
  have hsk := h.spoke_mem_of_shared (Ne.symm hki) a hek
  have he := h.intersection_unique j k (Ne.symm hkj) _ _ hej hek hsj hsk
  exact ((h.neighbourhood i).spoke_not_mem_cycle a ⟨a, he⟩).elim

include h in
theorem containing_card_le_two [Fintype I] (e : E) :
    (Finset.univ.filter (fun i => e ∈ Set.range (Φ i).edge)).card ≤ 2 := by
  classical
  by_cases hx : ∃ i j, i ≠ j ∧ e ∈ Set.range (Φ i).edge ∧ e ∈ Set.range (Φ j).edge
  · obtain ⟨i, j, hij, hei, hej⟩ := hx
    have hsub : Finset.univ.filter (fun k => e ∈ Set.range (Φ k).edge) ⊆ {i, j} := by
      intro k hk
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        h.eq_or_eq_of_mem hij hei hej (Finset.mem_filter.mp hk).2
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hone : (Finset.univ.filter (fun i => e ∈ Set.range (Φ i).edge)).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro i j hi hj
      by_contra hij
      exact hx ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
    omega

/-- Restrict a constellation to cycles all of which are stellar, or to
a collection which includes every stellar cycle (Lemma 11.6). -/
def restrict (s : Set I)
    (hs : (∀ i ∈ s, Nonempty ((Φ i).Stellar b)) ∨
      (∀ i, Nonempty ((Φ i).Stellar b) → i ∈ s)) :
    Constellation (fun i : s => Φ i.val) b where
  neighbourhood i := h.neighbourhood i.val
  stellar_or_covered i := by
    rcases hs with hall | hcontains
    · exact Or.inl (hall i.val i.property)
    · rcases h.stellar_or_covered i.val with hi | hi
      · exact Or.inl hi
      · refine Or.inr (fun k hk => ?_)
        obtain ⟨j, hj, he⟩ := hi k hk
        exact ⟨⟨j, hcontains j hj⟩, hj, he⟩
  private_or_neighbour i := by
    classical
    rcases h.private_or_neighbour i.val with hi | ⟨j, hji, hij, hj⟩
    · exact Or.inl hi.restrict
    · by_cases hjs : j ∈ s
      · exact Or.inr ⟨⟨j, hjs⟩, fun he => hji (congrArg Subtype.val he), hij, hj.restrict⟩
      · obtain ⟨e, hei, hej⟩ := hij
        refine Or.inl ⟨e, hei, fun k hek => ?_⟩
        rcases h.eq_or_eq_of_mem (Ne.symm hji) hei hej hek with hki | hkj
        · exact Subtype.ext hki
        · exact (hjs (hkj ▸ k.property)).elim
  intersection_unique i j hij e f hei hej hfi hfj :=
    h.intersection_unique i.val j.val (fun he => hij (Subtype.ext he)) e f hei hej hfi hfj
  nonstellar_disjoint i j hij hi hj :=
    h.nonstellar_disjoint i.val j.val (fun he => hij (Subtype.ext he)) hi hj

end Constellation
end ThomGame.Hypergraph
