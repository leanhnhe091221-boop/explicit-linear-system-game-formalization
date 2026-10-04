module

public import ThomGame.Pictures.BottomBoundaryGraph

/-!
# Prescribed lower-boundary realization

Move the lower boundary to its reversed upper word, realize the capped
graph, and bend the resulting diagram back. Empty boundaries use the
closed realization. All relation occurrences are retained; neither
connectedness nor absence of subdivision joints is required.
-/

@[expose] public section
namespace ThomGame.Pictures

namespace Diagram

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

def fromReversedTop (d : Diagram P w.reverse []) : Diagram P [] w :=
  (d.reverseDown.cast (List.reverse_reverse w) rfl).adjoint

theorem labels_fromReversedTop_perm (d : Diagram P w.reverse []) :
    d.fromReversedTop.labels.Perm d.labels := by
  exact (d.reverseDown.cast (List.reverse_reverse w) rfl).labels_adjoint_perm.trans
    ((by rw [labels_cast] : (d.reverseDown.cast (List.reverse_reverse w) rfl).labels.Perm
      d.reverseDown.labels).trans d.labels_reverseDown_perm)

theorem size_fromReversedTop (d : Diagram P w.reverse []) : d.fromReversedTop.size = d.size :=
  d.labels_fromReversedTop_perm.length_eq

end Diagram

namespace PortGraph

open RibbonConnectivity
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S} (G : PortGraph P [] w)

theorem exists_diagram_of_bottom_invariants
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P [] w, (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  by_cases hw : 0 < w.length
  · obtain ⟨d, hd⟩ := G.bottomTopGraph.exists_diagram_of_boundary_invariants
      (by simpa only [List.length_reverse] using hw) hn (G.bottomTop_eulerDefect.trans hEuler)
      (G.bottomTop_boundaryNoncrossing hnc) (G.bottomTop_boundarySeesComponents hsees)
    exact ⟨d.fromReversedTop, (Multiset.coe_eq_coe.mpr d.labels_fromReversedTop_perm).trans hd⟩
  · have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    exact G.exists_closed_diagram_of_saturated hn (G.rotationEuler_saturated_iff.mpr hEuler)

theorem exists_diagram_of_bottom_invariants_preserving
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P [] w,
      (d.labels : Multiset R) = (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = G.sign := by
  obtain ⟨d, hd⟩ := G.exists_diagram_of_bottom_invariants hn hEuler hnc hsees
  have hn' : d.size = Fintype.card G.Hub := by
    simpa [Diagram.size] using congrArg Multiset.card hd
  have hs : d.sign = G.sign := by
    let f : Multiset R →+ ZMod 2 := {
      toFun := fun rs => (rs.map P.parity).sum
      map_zero' := rfl
      map_add' := by intro a b; simp }
    have hh := congrArg f hd
    rw [map_sum] at hh
    change (Multiset.map P.parity (d.labels : Multiset R)).sum =
      ∑ h : G.Hub, (Multiset.map P.parity ([G.hubLabel h] : Multiset R)).sum at hh
    simpa [Diagram.sign, PortGraph.sign] using hh
  exact ⟨d, hd, hn', hs⟩

end PortGraph
end ThomGame.Pictures
