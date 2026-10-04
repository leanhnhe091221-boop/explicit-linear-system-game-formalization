module

public import ThomGame.Pictures.BlockFamilyClosed
public import ThomGame.Pictures.InvariantCycleMatching

/-!
# Closing every component of an Euler-saturating block family

The finite contraction trace leaves one vertex block per original
component. Each block has an invariant edge matching, so its actual
boundary can be closed separately. Composing these closed diagrams
preserves the complete relation multiset without a connectivity premise.
-/

@[expose] public section
namespace ThomGame.Pictures.BlockFamily

open Equiv CyclicBlock RibbonConnectivity
open scoped BigOperators

variable {R S D : Type*} [DecidableEq D] [Finite D]
    {P : InvolutionPresentation R S} {label : D → S} {r t : Perm D}
    (F : BlockFamily P label r t)

theorem exists_closed_diagram_of_saturated (ht : Function.Involutive t)
    (hl : ∀ x, label (t x) = label x)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) = F.relations := by
  classical
  obtain ⟨r', t', k, c, F', hterm, hrel⟩ := F.exists_terminal ht hl
  have hblock (i : F'.Index) : ∃ d : Diagram P [] [],
      (d.labels : Multiset R) = ((F'.block i).diagram.labels : Multiset R) := by
    have hm (x : D) : t' x ∈ (F'.block i).ports ↔ x ∈ (F'.block i).ports := by
      rw [F'.mem_ports, F'.mem_ports, F'.owner_eq_of_sameCycle (hterm x)]
    obtain ⟨d, hd⟩ := (F'.block i).cyclic.exists_filtered_diagram_of_invariant P t'
      (c.involutive ht) label (c.preserves_label ht label hl) hm (c.saturated ht hEuler)
    have hadj : d.adjoint.labels = [] := by
      apply List.perm_nil.mp
      simpa only [hd] using d.labels_adjoint_perm
    exact ⟨d.adjoint.comp (F'.block i).diagram, by simp only [Diagram.labels, hadj, List.nil_append]⟩
  have hsum (s : Finset F'.Index) : ∃ d : Diagram P [] [],
      (d.labels : Multiset R) = ∑ i ∈ s, ((F'.block i).diagram.labels : Multiset R) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨.identity [], by simp [Diagram.labels]⟩
    | @insert a s ha ih =>
      obtain ⟨d, hd⟩ := hblock a
      obtain ⟨e, he⟩ := ih
      refine ⟨d.comp e, ?_⟩
      change ((d.labels ++ e.labels : List R) : Multiset R) = _
      rw [← Multiset.coe_add, hd, he, Finset.sum_insert ha]
  obtain ⟨d, hd⟩ := hsum Finset.univ
  exact ⟨d, hd.trans hrel⟩

end ThomGame.Pictures.BlockFamily
