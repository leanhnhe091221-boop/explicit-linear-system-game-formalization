module

public import ThomGame.Pictures.CyclicBlockDiagrams
public import ThomGame.Pictures.ConnectedResidualMatching
public import ThomGame.Pictures.OrderedFiltering

/-!
# Matching the literal boundary of one full cyclic block

Numbering the block by its list positions transports its actual rotation
to the standard circle. The residual matching word is exactly the
filtered block word, so its relation-free diagram has the boundary
required to close the block's existing diagram.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CyclicBlock CircularPartition RibbonConnectivity

namespace ResidualMatching

variable {D S : Type*} [DecidableEq D] {n : Nat}

theorem word_transport (q : Perm (Fin n)) (t : Perm D) (e : Fin n ≃ D)
    (he : ∀ i, e (q i) = t (e i)) (label : D → S) :
    word q (fun i => label (e i)) = ((List.ofFn e).filter (moving t)).map label := by
  classical
  have hp : (fun i => q i ≠ i) = (fun i => moving t (e i) = true) := by
    funext i
    apply propext
    simp only [moving, decide_eq_true_eq, ← he]
    exact ⟨fun hn hh => hn (e.injective hh), fun hn hh => hn (congrArg e hh)⟩
  unfold word index
  rw [List.ofFn_comp' _ label]
  apply congrArg (List.map label)
  rw [hp]
  exact ofFn_subset_filter e (moving t)

end ResidualMatching

namespace CyclicBlock

variable {D : Type*} [DecidableEq D] {r : Perm D} {w : List D}

theorem formPerm_get_next (h : w.Nodup) (i : Fin w.length) :
    w.formPerm (w.get i) = w.get (finRotate w.length i) := by
  let : NeZero w.length := i.neZero
  have hfin : (⟨(i.val + 1) % w.length, Nat.mod_lt _ (Nat.pos_of_neZero _)⟩ : Fin w.length) =
      finRotate w.length i := by
    apply Fin.ext
    simp only [finRotate_apply, Fin.val_add]
    change (i.val + 1) % w.length = (i.val + 1 % w.length) % w.length
    exact (Nat.add_mod_mod _ _ _).symm
  exact (List.formPerm_apply_getElem w h i.val i.isLt).trans (congrArg w.get hfin)

namespace IsCycleWord

variable (h : IsCycleWord r w) (hall : ∀ x : D, x ∈ w)

noncomputable def fullEnumeration : Fin w.length ≃ D :=
  Equiv.ofBijective w.get ⟨h.nodup.injective_get, fun x => List.get_of_mem (hall x)⟩

theorem fullEnumeration_rotation (i : Fin w.length) :
    r (h.fullEnumeration hall i) = h.fullEnumeration hall (finRotate w.length i) :=
  (h.rotation _ (List.get_mem w i)).trans (formPerm_get_next h.nodup i)

theorem fullEnumeration_list : List.ofFn (h.fullEnumeration hall) = w := List.ofFn_get w

variable [Finite D]

include h hall in
theorem exists_filtered_diagram {R S : Type*} (P : InvolutionPresentation R S)
    (t : Perm D) (ht : Function.Involutive t) (label : D → S)
    (hl : ∀ x, label (t x) = label x)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    ∃ d : Diagram P ((w.filter (moving t)).map label) [], d.labels = [] := by
  let e := h.fullEnumeration hall
  let q : Perm (Fin w.length) := (e.trans t).trans e.symm
  have hq (i : Fin w.length) : e (q i) = t (e i) := e.apply_symm_apply _
  have hqi : Function.Involutive q := by
    intro i
    apply e.injective
    rw [hq, hq, ht]
  have hql (i : Fin w.length) : label (e (q i)) = label (e i) := by rw [hq, hl]
  have hr : ∀ i, r (e i) = e (finRotate _ i) := h.fullEnumeration_rotation hall
  have hE : RotationEuler.count (finRotate _) q =
      2 * Nat.card (Component (finRotate _) q) := by
    rw [RotationEuler.count_congr _ _ r t e hr (fun i => (hq i).symm),
      Nat.card_congr (componentCongrEquiv _ _ r t e hr (fun i => (hq i).symm))]
    exact hEuler
  obtain ⟨d, hd⟩ := ResidualMatching.exists_diagram_of_euler q hqi (fun i => label (e i)) hql P hE
  have hw : ResidualMatching.word q (fun i => label (e i)) = (w.filter (moving t)).map label := by
    rw [ResidualMatching.word_transport q t e hq label, h.fullEnumeration_list hall]
  exact ⟨d.cast hw rfl, (Diagram.labels_cast _ _ _).trans hd⟩

end IsCycleWord
end CyclicBlock
end ThomGame.Pictures
