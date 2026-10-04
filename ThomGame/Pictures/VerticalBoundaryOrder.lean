module

public import ThomGame.Pictures.VerticalNoncrossing

/-!
# Vertical composition preserves the actual ordered boundary condition

After all real seam indices have been exchanged and deleted, the
retained ports are exactly the outer boundary. Its increasing numbering
and its first-return permutation are identified with the actual composed
graph. This discharges vertical closure without a planar hypothesis.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}

theorem outer_numberedRemaining (x : SeamBoundary u v w) :
    IsOuter x ↔ numberedSeamRemaining u v w v.length (seamOrderIndex u v w x) :=
  ((numberedSeamRemaining_index u v w v.length x).trans (SeamRemaining_all u v w x)).symm

def outerSeamIndex (u v w : List S) :
    BoundaryIndex u w ≃ Subtype (numberedSeamRemaining u v w v.length) :=
  (outerPorts (v := v)).trans
    ((seamOrderIndex u v w).subtypeEquiv outer_numberedRemaining)

def outerSeamNumbering (u v w : List S) :
    Fin (u.length + w.length) ≃ Subtype (numberedSeamRemaining u v w v.length) :=
  (boundaryOrderIndex u w).symm.trans (outerSeamIndex u v w)

theorem outerSeamNumbering_index (i : BoundaryIndex u w) :
    outerSeamNumbering u v w (boundaryOrderIndex u w i) = outerSeamIndex u v w i := by
  simp [outerSeamNumbering]

theorem outerSeamNumbering_val (i : Fin (u.length + w.length)) :
    (outerSeamNumbering u v w i).val.val =
      if i.val < u.length then i.val else i.val + 2 * v.length := by
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex u w).surjective i
  rw [outerSeamNumbering_index]
  cases i with
  | inl i =>
    change (seamOrderIndex u v w (.inl (.inl i))).val = _
    rw [seamOrderIndex_top_val, boundaryOrderIndex_top_val, ite_eq_left i.isLt]
  | inr i =>
    have hn : ¬ (boundaryOrderIndex u w (.inr i)).val < u.length := by
      rw [boundaryOrderIndex_bottom_val]
      omega
    rw [ite_eq_right hn]
    change (seamOrderIndex u v w (.inr (.inr i))).val = _
    rw [seamOrderIndex_bottom_val, boundaryOrderIndex_bottom_val, Fin.val_rev]
    omega

theorem outerSeamNumbering_strictMono :
    StrictMono (fun i : Fin (u.length + w.length) => (outerSeamNumbering u v w i).val) := by
  intro i j hij
  change i.val < j.val at hij
  change (outerSeamNumbering u v w i).val.val < (outerSeamNumbering u v w j).val.val
  rw [outerSeamNumbering_val, outerSeamNumbering_val]
  split_ifs <;> omega

theorem numberedPartialSeam_all_index (G : PortGraph P u v) (H : PortGraph P v w)
    (x : SeamBoundary u v w) :
    numberedPartialSeam G H v.length (seamOrderIndex u v w x) =
      seamOrderIndex u v w (boundarySeamCircuit G H x) := by
  rw [numberedPartialSeam_index, partialBoundarySwap_all]
  rfl

theorem outerSeamIndex_next (G : PortGraph P u v) (H : PortGraph P v w) (i : BoundaryIndex u w) :
    perm (numberedPartialSeam G H v.length) (numberedSeamRemaining u v w v.length)
      (outerSeamIndex u v w i) = outerSeamIndex u v w ((G.comp H).boundaryNext i) := by
  have he := perm_subtypeEquiv (boundarySeamCircuit G H) (numberedPartialSeam G H v.length)
    (seamOrderIndex u v w) (numberedPartialSeam_all_index G H) IsOuter
    (numberedSeamRemaining u v w v.length) outer_numberedRemaining (outerPorts i)
  rw [outerPorts_verticalNext, ← boundaryNext_comp] at he
  exact he

theorem outerSeamNumbering_next (G : PortGraph P u v) (H : PortGraph P v w)
    (i : Fin (u.length + w.length)) :
    perm (numberedPartialSeam G H v.length) (numberedSeamRemaining u v w v.length)
      (outerSeamNumbering u v w i) = outerSeamNumbering u v w ((G.comp H).numberedBoundaryNext i) := by
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex u w).surjective i
  rw [outerSeamNumbering_index, numberedBoundaryNext_index, outerSeamNumbering_index,
    outerSeamIndex_next]

/-- Actual vertical composition preserves both circular orbit direction
and exclusion of alternating distinct boundary orbits. -/
theorem boundaryNoncrossing_comp (G : PortGraph P u v) (H : PortGraph P v w)
    (hG : G.BoundaryNoncrossing) (hH : H.BoundaryNoncrossing) : (G.comp H).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  have hn := (numberedPartialSeam_noncrossing G H hG hH v.length le_rfl).renumber
    (outerSeamNumbering u v w) outerSeamNumbering_strictMono
  have he : CircularPartition.renumber (outerSeamNumbering u v w)
      (perm (numberedPartialSeam G H v.length) (numberedSeamRemaining u v w v.length)) =
      (G.comp H).numberedBoundaryNext := by
    apply Equiv.ext
    intro i
    rw [renumber_apply, outerSeamNumbering_next, Equiv.symm_apply_apply]
  rwa [he] at hn

end ThomGame.Pictures.PortGraph
