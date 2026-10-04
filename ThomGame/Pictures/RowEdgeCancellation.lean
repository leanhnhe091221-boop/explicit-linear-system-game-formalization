module

public import ThomGame.Pictures.RowTriangleBlocks
public import ThomGame.Pictures.BlockReplacement
public import ThomGame.Pictures.ClosedMinimalOddState

/-!
# Cancelling equally labelled opposite hubs in an actual closed row graph

The actual cyclic hub blocks are merged across the chosen edge and filled
by a relation-free triangle cancellation block. Closing this block family
gives a genuine diagram with two fewer hubs and the same sign. Minimal
odd states therefore force equal orientations on equally labelled edges.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint]

theorem exists_row_edge_cancelled (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i)
    (hl : G.hubLabel h = G.hubLabel k) (hf : G.hubFlip h ≠ G.hubFlip k)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0) :
    ∃ d : SolutionGroup.RowDiagram A [] [],
      (d.labels : Multiset R) + [G.hubLabel h, G.hubLabel h] =
        (∑ j : G.Hub, ([G.hubLabel j] : Multiset R)) ∧
      d.size + 2 = Fintype.card G.Hub ∧ d.sign = G.sign := by
  have hn (j : G.Hub) : 0 < ((SolutionGroup.triangularPresentation A).word (G.hubLabel j)).length := by
    change 0 < 3
    decide +kernel
  have hne : h ≠ k := by
    intro hh
    subst k
    exact G.pairing.ne_self (.hub h i) he
  have hsep : ¬ G.rotation.SameCycle (.hub h i) (G.pairing.twin (.hub h i)) := by
    intro hc
    rw [he] at hc
    exact hne (Sum.inl.inj (Sum.inr.inj ((G.rotation_sameCycle_iff _ _).mp hc)))
  obtain ⟨B, ha, hb⟩ := G.exists_row_triangle_cancel_block
    (SolutionGroup.triangularPresentation A) G.rotation (fun _ _ => rfl) h k i he hl hf hsep
  let F := G.closedBlockFamily hn
  obtain ⟨d, hd⟩ := F.exists_closed_diagram_cancel_merge G.pairing.involutive G.pairing.label_twin
    (G.rotationEuler_saturated_iff.mpr hEuler) (.hub h i) hsep B ha hb
  have hL : (F.block (F.owner (.hub h i))).diagram.labels = [G.hubLabel h] :=
    G.hubBlock_labels h (hn h)
  have hR : (F.block (F.owner (G.pairing.twin (.hub h i)))).diagram.labels = [G.hubLabel k] := by
    rw [he]
    exact G.hubBlock_labels k (hn k)
  have hLR := congrArg₂ (fun x y : List R =>
    (d.labels : Multiset R) + (x : Multiset R) + (y : Multiset R)) hL hR
  have hd' := hLR.symm.trans hd
  rw [← hl, add_assoc] at hd'
  have hrel := hd'.trans (G.closedBlockFamily_relations hn)
  refine ⟨d, hrel, ?_, ?_⟩
  · simpa [Diagram.size] using congrArg Multiset.card hrel
  · let f : Multiset R →+ ZMod 2 := {
      toFun := fun rs => (rs.map (SolutionGroup.triangularPresentation A).parity).sum
      map_zero' := rfl
      map_add' := by intro a b; simp }
    have hh := congrArg f hrel
    rw [map_add, map_sum] at hh
    change (Multiset.map (SolutionGroup.triangularPresentation A).parity (d.labels : Multiset R)).sum +
        (Multiset.map (SolutionGroup.triangularPresentation A).parity
          (([G.hubLabel h] : Multiset R) + [G.hubLabel h])).sum =
      ∑ j : G.Hub, (Multiset.map (SolutionGroup.triangularPresentation A).parity
        ([G.hubLabel j] : Multiset R)).sum at hh
    simpa [Diagram.sign, PortGraph.sign, InvolutionDerivation.parity_self_add] using hh

namespace ClosedMinimalOddState

theorem row_same_flip_of_same_label_edge (H : G.ClosedMinimalOddState)
    (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i) (hl : G.hubLabel h = G.hubLabel k) :
    G.hubFlip h = G.hubFlip k := by
  by_contra hf
  obtain ⟨d, _, hc, hs⟩ := exists_row_edge_cancelled h k i he hl hf H.euler
  have hm := H.minimal d (hs.trans H.sign)
  omega

end ClosedMinimalOddState
end ThomGame.Pictures.PortGraph
