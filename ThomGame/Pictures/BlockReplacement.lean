module

public import ThomGame.Pictures.DisconnectedBlockFamily

/-!
# Replacing one actual cyclic block before closing the graph

A replacement may have a different list starting point but must use
exactly the same rotation orbit. The other blocks and all edge data
remain the same. The relation multiset identity records both the removed
and inserted diagram; in particular a relation-free replacement removes
exactly the old occurrences.
-/

@[expose] public section
namespace ThomGame.Pictures.BlockFamily

open Equiv CyclicBlock CycleSurgery RibbonConnectivity
open scoped Classical BigOperators

variable {R S D : Type*} [DecidableEq D] [Finite D]
  {P : InvolutionPresentation R S} {label : D → S} {r t : Perm D}
  (F : BlockFamily P label r t) (i : F.Index) (B : DiagramBlock P label r t)
  (hm : ∀ x, x ∈ B.ports ↔ F.owner x = i)

noncomputable def replace : BlockFamily P label r t where
  Index := F.Index
  block j := if j = i then B else F.block j
  owner := F.owner
  mem_ports x j := by
    split_ifs with hj
    · subst j
      exact hm x
    · exact F.mem_ports x j

omit [Finite D] in
theorem replace_relations :
    (F.replace i B hm).relations + ((F.block i).diagram.labels : Multiset R) =
      F.relations + (B.diagram.labels : Multiset R) := by
  have he := Finset.sum_erase_add (Finset.univ : Finset F.Index)
    (fun j => ((F.block j).diagram.labels : Multiset R)) (Finset.mem_univ i)
  have hn := Finset.sum_erase_add (Finset.univ : Finset F.Index)
    (fun j => ((if j = i then B else F.block j).diagram.labels : Multiset R))
    (Finset.mem_univ i)
  have ha : (∑ j ∈ Finset.univ.erase i,
      ((if j = i then B else F.block j).diagram.labels : Multiset R)) =
      ∑ j ∈ Finset.univ.erase i, ((F.block j).diagram.labels : Multiset R) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [ha] at hn
  rw [ite_eq_left (rfl : i = i)] at hn
  change (∑ j : F.Index, ((if j = i then B else F.block j).diagram.labels : Multiset R)) + _ =
    (∑ j : F.Index, ((F.block j).diagram.labels : Multiset R)) + _
  rw [← hn, ← he]
  ac_rfl

omit hm in
theorem replacement_mem_of_common {a : D} (ha : a ∈ B.ports) (hi : F.owner a = i) (x : D) :
    x ∈ B.ports ↔ F.owner x = i := by
  have ha' := (F.mem_ports a i).mpr hi
  exact (B.cyclic.mem_iff_sameCycle ha x).trans
    (((F.block i).cyclic.mem_iff_sameCycle ha' x).symm.trans (F.mem_ports x i))

variable {F i B hm}

theorem exists_closed_diagram_cancel_merge (F : BlockFamily P label r t)
    (ht : Function.Involutive t) (hl : ∀ x, label (t x) = label x)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t))
    (a : D) (hr : ¬ r.SameCycle a (t a))
    (B : DiagramBlock P label (splice r a (t a)) (splice t a (t a)))
    (ha : a ∈ B.ports) (hb : B.diagram.labels = []) :
    ∃ d : Diagram P [] [],
      (d.labels : Multiset R) + ((F.block (F.owner a)).diagram.labels : Multiset R) +
        ((F.block (F.owner (t a))).diagram.labels : Multiset R) = F.relations := by
  let F' := F.merge ht hl a hr
  let i : F'.Index := ⟨F.owner a, F.owners_ne a hr⟩
  have hi : F'.owner a = i := by
    apply Subtype.ext
    change (if F.owner a = F.owner (t a) then F.owner a else F.owner a) = F.owner a
    split_ifs <;> rfl
  have hm := F'.replacement_mem_of_common i B ha hi
  let F'' := F'.replace i B hm
  have hti := RotationEuler.removed_pair_involutive t ht a
  have hli (x : D) : label (splice t a (t a) x) = label x := by
    rcases EdgeContraction.removed_pair_value t ht a x with hx | hx
    · rw [hx]
    · rw [hx, hl]
  obtain ⟨d, hd⟩ := F''.exists_closed_diagram_of_saturated hti hli
    (RotationEuler.contractEdge_saturated r t ht hEuler a hr)
  have hrel := F'.replace_relations i B hm
  have hblock : (F'.block i).diagram.labels =
      (F.block (F.owner a)).diagram.labels ++ (F.block (F.owner (t a))).diagram.labels := by
    exact (F.mergedBlock_labels ht hl a hr i).trans (ite_eq_left rfl)
  rw [hblock, hb, Multiset.coe_nil, add_zero, F.merge_relations ht hl a hr] at hrel
  refine ⟨d, ?_⟩
  rw [hd, add_assoc, Multiset.coe_add]
  exact hrel

end ThomGame.Pictures.BlockFamily
