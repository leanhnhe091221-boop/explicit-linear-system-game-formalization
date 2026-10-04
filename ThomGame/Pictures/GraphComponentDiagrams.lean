module

public import ThomGame.Pictures.SelectedClosedGraph

/-!
# Diagram witnesses for actual closed graph components

Every component of an Euler-saturated closed graph has a closed diagram
with exactly its relation occurrences. Size and sign are the actual
component weights, independently of any original diagram or smoothing.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} (G : PortGraph P [] [])

theorem exists_component_diagram
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (k : G.GraphComponent) :
    ∃ d : Diagram P [] [],
      (d.labels : Multiset R) =
        (∑ h : G.Hub, if G.hubComponent h = k then ([G.hubLabel h] : Multiset R) else 0) ∧
      d.size = G.componentWeight k (fun _ => (1 : Nat)) ∧
      d.sign = G.componentWeight k P.parity := by
  obtain ⟨d, hd⟩ := (G.componentSelection k).exists_closed_diagram hn hEuler
  simp only [G.componentSelection_hub] at hd
  refine ⟨d, hd, ?_, ?_⟩
  · have hh := congrArg Multiset.card hd
    simp only [Multiset.coe_card, Multiset.card_sum] at hh
    refine hh.trans ?_
    unfold componentWeight
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : G.hubComponent x = k <;> simp [hx]
  · let f : Multiset R →+ ZMod 2 := {
      toFun rs := (rs.map P.parity).sum
      map_zero' := rfl
      map_add' rs ss := by simp }
    have hh := congrArg f hd
    rw [map_sum] at hh
    change (Multiset.map P.parity (d.labels : Multiset R)).sum = _ at hh
    simp only [Multiset.map_coe, Multiset.sum_coe] at hh
    refine hh.trans ?_
    unfold componentWeight
    apply Finset.sum_congr rfl
    intro x _
    change (Multiset.map P.parity
      (if G.hubComponent x = k then ([G.hubLabel x] : Multiset R) else 0)).sum = _
    by_cases hx : G.hubComponent x = k <;> simp [hx]

end ThomGame.Pictures.PortGraph
