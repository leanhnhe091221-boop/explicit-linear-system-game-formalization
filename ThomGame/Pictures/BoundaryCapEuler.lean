module

public import ThomGame.Pictures.BoundaryCapSmoothing

/-!
# Capped Euler saturation without connectedness

The upward boundary star is an actual primitive graph. Composition with
it has zero Euler defect by the proved boundary-order gluing theorem.
Selective smoothing removes exactly the new seams, and the explicit
first-return calculation identifies its pairing and rotation with the
prescribed capped permutations of the original graph.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity RotationEuler
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P w [])

theorem boundaryClosure_eulerDefect (hnc : G.BoundaryNoncrossing)
    (hsees : G.BoundarySeesComponents) :
    eulerDefect G.boundaryClosure.pairing.perm G.boundaryClosure.circuitStep =
      eulerDefect G.pairing.perm G.circuitStep := by
  have hs : eulerDefect G.boundaryStar.pairing.perm G.boundaryStar.circuitStep = 0 :=
    eulerDefect_up (P.adjoinRelation w 0) none
  have h := eulerDefect_comp G.boundaryStar (G.adjoinGraph w)
    (boundarySeesComponents_up (P.adjoinRelation w 0) none) (G.adjoin_boundarySeesComponents w hsees)
    (boundaryNoncrossing_up (P.adjoinRelation w 0) none) (G.adjoin_boundaryNoncrossing w hnc)
  exact h.trans (by rw [hs, G.adjoin_eulerDefect, zero_add])

theorem cappedRotation_saturated_general (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm) := by
  obtain ⟨H, d, hd, hc⟩ := Smoothing.exists_selected_without_circles G.boundaryClosure
    G.boundaryClosureRemove G.boundaryClosure_selectedAccessible
  let e := d.selectedTerminalEquiv G.boundaryClosureRemove hd hc
  let i : G.Dart ≃ H.Dart := G.boundaryClosurePorts.trans e.symm
  have hi (x : G.Dart) : e (i x) = G.boundaryClosurePorts x := e.apply_symm_apply _
  have he (x : G.Dart) : d.portEmbedding (i x) = G.boundaryClosurePort x :=
    congrArg Subtype.val (hi x)
  have hr (x : G.Dart) : H.rotation (i x) = i (G.cappedRotation x) := by
    apply d.portEmbedding.injective
    rw [d.portRotation, he, he, G.boundaryClosure_rotation]
  have ht (x : G.Dart) : H.pairing.perm (i x) = i (G.pairing.perm x) := by
    apply d.portEmbedding.injective
    change d.portEmbedding (H.pairing.twin (i x)) = d.portEmbedding (i (G.pairing.twin x))
    rw [d.selected_twin_return G.boundaryClosureRemove hd hc]
    change (MarkedReturn.perm (G.boundaryClosure.selectedStep G.boundaryClosureRemove)
      (G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove) (e (i x))).val = _
    rw [hi, G.boundaryClosure_return, he]
  have hnC : ∀ h : G.boundaryClosure.Hub,
      0 < ((P.adjoinRelation w 0).word (G.boundaryClosure.hubLabel h)).length := by
    rintro (h | h)
    · exact hw
    · exact hn h
  have hC : count G.boundaryClosure.rotation G.boundaryClosure.pairing.perm =
      2 * Nat.card (Component G.boundaryClosure.rotation G.boundaryClosure.pairing.perm) :=
    G.boundaryClosure.rotationEuler_saturated_iff.mpr
      ((G.boundaryClosure_eulerDefect hnc hsees).trans hEuler)
  have hH := d.rotationEuler_saturated hnC hC
  rw [count_congr G.cappedRotation G.pairing.perm H.rotation H.pairing.perm i hr ht,
    Nat.card_congr (componentCongrEquiv G.cappedRotation G.pairing.perm H.rotation H.pairing.perm i hr ht)]
  exact hH

theorem exists_diagram_of_boundary_invariants (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P w [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) :=
  G.exists_diagram_of_capped_saturated hw hn (G.cappedRotation_saturated_general hw hn hEuler hnc hsees)

end ThomGame.Pictures.PortGraph
