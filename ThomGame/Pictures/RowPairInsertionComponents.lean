module

public import ThomGame.Pictures.RowPairInsertionReturn
public import ThomGame.Pictures.GraphConnectivity
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pair insertion does not split an original graph component

Every replaced edge has an actual path through the two new hubs. Thus
old connectivity is preserved, and every new dart is connected to an
old one. The induced component map is surjective. Components may merge
without a face hypothesis; equality is not asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open RibbonConnectivity
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowPairInsertion) (o : Bool)

theorem fresh_connected_zero (b : Bool) (i : Fin 3) :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.fresh b i) (s.fresh false 0) := by
  cases b
  · exact (s.graph o).connected_of_same_vertex rfl
  · have h : Connected (s.graph o).pairing.perm (s.graph o).circuitStep
        (s.fresh true 0) (s.fresh false 0) := by
      have hh := Connected.edge (p := (s.graph o).pairing.perm)
        (f := (s.graph o).circuitStep) (s.fresh true 0)
      change Connected _ _ _ (s.pairing.twin (s.fresh true 0)) at hh
      rw [s.twin_spoke] at hh
      exact hh
    exact ((s.graph o).connected_of_same_vertex (a := s.fresh true i) (b := s.fresh true 0) rfl).trans h

theorem fresh_connected (b c : Bool) (i j : Fin 3) :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.fresh b i) (s.fresh c j) :=
  (s.fresh_connected_zero o b i).trans (s.fresh_connected_zero o c j).symm

theorem first_connected_fresh :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.old s.first) (s.fresh false 1) := by
  have h := Connected.edge (p := (s.graph o).pairing.perm)
    (f := (s.graph o).circuitStep) (s.old s.first)
  change Connected _ _ _ (s.pairing.twin (s.old s.first)) at h
  rwa [s.twin_first] at h

theorem fresh_connected_old (b : Bool) (i : Fin 3) :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.fresh b i) (s.old s.first) :=
  (s.fresh_connected o b false i 1).trans (s.first_connected_fresh o).symm

theorem first_edge_path :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep
      (s.old s.first) (s.old (G.pairing.twin s.first)) := by
  have ht := Connected.edge (p := (s.graph o).pairing.perm)
    (f := (s.graph o).circuitStep) (s.old (G.pairing.twin s.first))
  change Connected _ _ _ (s.pairing.twin (s.old (G.pairing.twin s.first))) at ht
  rw [s.twin_partner_first] at ht
  exact (s.first_connected_fresh o).trans ((s.fresh_connected o false true 1 1).trans ht.symm)

theorem second_edge_path :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep
      (s.old s.second) (s.old (G.pairing.twin s.second)) := by
  have hs := Connected.edge (p := (s.graph o).pairing.perm)
    (f := (s.graph o).circuitStep) (s.old s.second)
  have ht := Connected.edge (p := (s.graph o).pairing.perm)
    (f := (s.graph o).circuitStep) (s.old (G.pairing.twin s.second))
  change Connected _ _ _ (s.pairing.twin (s.old s.second)) at hs
  change Connected _ _ _ (s.pairing.twin (s.old (G.pairing.twin s.second))) at ht
  rw [s.twin_second] at hs
  rw [s.twin_partner_second] at ht
  exact hs.trans ((s.fresh_connected o false true 2 2).trans ht.symm)

theorem old_edge_path (x : G.Dart) :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.old x) (s.old (G.pairing.twin x)) := by
  by_cases h1 : x = s.first
  · subst x
    exact s.first_edge_path o
  by_cases h2 : x = s.second
  · subst x
    exact s.second_edge_path o
  by_cases ht1 : x = G.pairing.twin s.first
  · subst x
    rw [G.pairing.involutive]
    exact (s.first_edge_path o).symm
  by_cases ht2 : x = G.pairing.twin s.second
  · subst x
    rw [G.pairing.involutive]
    exact (s.second_edge_path o).symm
  have h := Connected.edge (p := (s.graph o).pairing.perm)
    (f := (s.graph o).circuitStep) (s.old x)
  change Connected _ _ _ (s.pairing.twin (s.old x)) at h
  rwa [s.twin_old_away x h1 h2 ht1 ht2] at h

theorem old_connected {x y : G.Dart} (h : Connected G.pairing.perm G.circuitStep x y) :
    Connected (s.graph o).pairing.perm (s.graph o).circuitStep (s.old x) (s.old y) := by
  apply h.lift s.old ⟨Connected.refl, Connected.symm, Connected.trans⟩ (s.old_edge_path o)
  intro x
  have hr := (s.graph o).connected_rotation (s.old (G.pairing.twin x))
  rw [s.rotation_old] at hr
  exact (s.old_edge_path o x).trans hr

noncomputable def componentMap : Component G.pairing.perm G.circuitStep →
    Component (s.graph o).pairing.perm (s.graph o).circuitStep :=
  Quotient.lift (fun x => component (s.graph o).pairing.perm (s.graph o).circuitStep (s.old x))
    (fun _ _ h => (component_eq_iff _ _ _ _).mpr (s.old_connected o h))

theorem componentMap_surjective : Function.Surjective (s.componentMap o) := by
  intro c
  refine Quotient.inductionOn c fun x => ?_
  obtain ⟨x, rfl⟩ := s.ports.surjective x
  rcases x with x | ⟨b, i⟩
  · exact ⟨component G.pairing.perm G.circuitStep x, rfl⟩
  · exact ⟨component G.pairing.perm G.circuitStep s.first,
      (component_eq_iff _ _ _ _).mpr (s.fresh_connected_old o b i).symm⟩

theorem component_card_le :
    Nat.card (Component (s.graph o).pairing.perm (s.graph o).circuitStep) ≤
      Nat.card (Component G.pairing.perm G.circuitStep) :=
  Nat.card_le_card_of_surjective (s.componentMap o) (s.componentMap_surjective o)

end ThomGame.Pictures.PortGraph.RowPairInsertion
