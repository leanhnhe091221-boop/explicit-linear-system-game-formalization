module

public import ThomGame.Pictures.DiagramSelection
public import ThomGame.Pictures.GraphComponentCounts
public import ThomGame.Pictures.Surgery

/-!
# Component diagrams and minimal odd diagrams

Every actual vertex component of a closed diagram supplies a closed diagram
with exactly its selected relation occurrences. Component signs sum to the
original sign. Consequently all relation hubs of a minimum-size closed odd
diagram belong to one component. Components consisting only of wires may
still exist; no claim about their geometric placement is made.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

variable {u v : List S} (G : PortGraph P u v)

def hubComponent (h : G.Hub) : G.GraphComponent := G.graphComponent (.inr (.inl h))

noncomputable def componentSelection (k : G.GraphComponent) : G.Selection := by
  classical
  exact {
    pick x := decide (G.graphComponent x = k)
    edge a := by
      have he := (G.graphComponent_eq_iff _ _).mpr (G.reachable_edge a)
      rw [he] }

theorem componentSelection_hub (k : G.GraphComponent) (h : G.Hub) :
    (G.componentSelection k).hub h = true ↔ G.hubComponent h = k := by
  classical
  simp [componentSelection, Selection.hub, hubComponent]

noncomputable def componentWeight {A : Type*} [AddCommMonoid A]
    (k : G.GraphComponent) (weight : R → A) : A := by
  classical
  exact ∑ h : G.Hub, if G.hubComponent h = k then weight (G.hubLabel h) else 0

theorem sum_componentWeight {A : Type*} [AddCommMonoid A] [Fintype G.GraphComponent]
    (weight : R → A) :
    (∑ k : G.GraphComponent, G.componentWeight k weight) = ∑ h : G.Hub, weight (G.hubLabel h) := by
  classical
  unfold componentWeight
  rw [Finset.sum_comm]
  simp

theorem exists_odd_component (hs : G.sign = 1) :
    ∃ k : G.GraphComponent, G.componentWeight k P.parity = 1 := by
  classical
  let : Fintype G.GraphComponent := Fintype.ofFinite _
  by_contra h
  have hz : ∀ k : G.GraphComponent, G.componentWeight k P.parity = 0 := by
    intro k
    rcases InvolutionDerivation.parity_cases (G.componentWeight k P.parity) with hk | hk
    · exact hk
    · exact (h ⟨k, hk⟩).elim
  have he := G.sum_componentWeight P.parity
  simp only [hz, Finset.sum_const_zero] at he
  exact zero_ne_one (he.trans hs)

end PortGraph

namespace Diagram

variable (d : Diagram P [] [])

/-- An actual closed diagram obtained by retaining a whole vertex component. -/
noncomputable def componentDiagram (k : d.graph.GraphComponent) : Diagram P [] [] :=
  d.select (d.graph.componentSelection k)

theorem componentDiagram_weight {A : Type*} [AddCommMonoid A]
    (k : d.graph.GraphComponent) (weight : R → A) :
    ((d.componentDiagram k).labels.map weight).sum = d.graph.componentWeight k weight := by
  classical
  exact (d.sum_labels_select (d.graph.componentSelection k) weight).trans (by
    apply Finset.sum_congr rfl
    intro h _
    simp only [d.graph.componentSelection_hub])

theorem componentDiagram_sign (k : d.graph.GraphComponent) :
    (d.componentDiagram k).sign = d.graph.componentWeight k P.parity :=
  d.componentDiagram_weight k P.parity

theorem componentDiagram_size (k : d.graph.GraphComponent) :
    (d.componentDiagram k).size = d.graph.componentWeight k (fun _ => (1 : Nat)) := by
  simpa [size] using d.componentDiagram_weight k (fun _ => (1 : Nat))

theorem componentDiagram_size_le (k : d.graph.GraphComponent) :
    (d.componentDiagram k).size ≤ d.size := d.size_select_le _

/-- Minimality forces every relation hub into any component of odd sign. -/
theorem minimal_odd_hubs_in_component (hmin : d.Minimal) (hs : d.sign = 1)
    (k : d.graph.GraphComponent) (hk : d.graph.componentWeight k P.parity = 1) :
    ∀ h : d.graph.Hub, d.graph.hubComponent h = k := by
  classical
  have hle := hmin (d.componentDiagram k) ((d.componentDiagram_sign k).trans (hk.trans hs.symm))
  rw [d.componentDiagram_size, ← d.graph_hub_card] at hle
  intro h
  by_contra hh
  have hlt : d.graph.componentWeight k (fun _ => (1 : Nat)) < Fintype.card d.graph.Hub := by
    unfold PortGraph.componentWeight
    calc
      (∑ x : d.graph.Hub, if d.graph.hubComponent x = k then 1 else 0) <
          ∑ _ : d.graph.Hub, (1 : Nat) := by
        apply Finset.sum_lt_sum
        · intro x _; split <;> omega
        · exact ⟨h, Finset.mem_univ _, by simp [hh]⟩
      _ = Fintype.card d.graph.Hub := by simp
  exact (Nat.not_lt_of_ge hle) hlt

theorem minimal_odd_exists_component (hmin : d.Minimal) (hs : d.sign = 1) :
    ∃ k : d.graph.GraphComponent, d.graph.componentWeight k P.parity = 1 ∧
      ∀ h : d.graph.Hub, d.graph.hubComponent h = k := by
  obtain ⟨k, hk⟩ := d.graph.exists_odd_component (d.graph_sign.trans hs)
  exact ⟨k, hk, d.minimal_odd_hubs_in_component hmin hs k hk⟩

theorem minimal_odd_hubs_reachable (hmin : d.Minimal) (hs : d.sign = 1)
    (h j : d.graph.Hub) : d.graph.Reachable (.inr (.inl h)) (.inr (.inl j)) := by
  obtain ⟨k, _, hk⟩ := d.minimal_odd_exists_component hmin hs
  exact (d.graph.graphComponent_eq_iff _ _).mp ((hk h).trans (hk j).symm)

end Diagram
end ThomGame.Pictures
