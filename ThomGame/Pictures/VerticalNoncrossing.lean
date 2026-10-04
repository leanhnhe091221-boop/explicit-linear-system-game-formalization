module

public import ThomGame.Pictures.VerticalSeamOrder

/-!
# Noncrossing under all actual vertical seam exchanges

Induction over the real seam indices uses their proved adjacency after
the earlier indices have been deleted. Every induction state is the
first return of the explicit partial seam permutation, not a free choice
of a partition with the desired properties.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn CycleSurgery CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}

noncomputable def numberedPartialSeam (G : PortGraph P u v) (H : PortGraph P v w) (k : Nat) :
    Perm (NumberedSeam u v w) :=
  (((seamOrderIndex u v w).symm.trans
    (partialBoundarySwap u v w k * Equiv.sumCongr G.boundaryNext H.boundaryNext)).trans
    (seamOrderIndex u v w))

theorem numberedPartialSeam_index (G : PortGraph P u v) (H : PortGraph P v w)
    (k : Nat) (x : SeamBoundary u v w) :
    numberedPartialSeam G H k (seamOrderIndex u v w x) =
      seamOrderIndex u v w
        (partialBoundarySwap u v w k (Equiv.sumCongr G.boundaryNext H.boundaryNext x)) := by
  simp [numberedPartialSeam]

theorem numberedPartialSeam_step (G : PortGraph P u v) (H : PortGraph P v w) (i : Fin v.length) :
    numberedPartialSeam G H (i.val + 1) =
      splice (numberedPartialSeam G H i.val)
        (retainedSeamLeft u v w i).val (retainedSeamRight u v w i).val := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (seamOrderIndex u v w).surjective x
  rw [splice_apply, numberedPartialSeam_index, numberedPartialSeam_index,
    partialBoundarySwap_step, Perm.mul_apply]
  exact (seamOrderIndex u v w).injective.map_swap _ _ _

theorem numberedPartialSeam_zero_index (G : PortGraph P u v) (H : PortGraph P v w)
    (x : Fin (u.length + v.length) ⊕ Fin (v.length + w.length)) :
    numberedPartialSeam G H 0 (finSumFinEquiv x) =
      finSumFinEquiv (Equiv.sumCongr G.numberedBoundaryNext H.numberedBoundaryNext x) := by
  cases x with
  | inl x =>
    obtain ⟨i, rfl⟩ := (boundaryOrderIndex u v).surjective x
    change numberedPartialSeam G H 0 (seamOrderIndex u v w (.inl i)) = _
    rw [numberedPartialSeam_index, partialBoundarySwap_zero]
    change seamOrderIndex u v w (.inl (G.boundaryNext i)) =
      finSumFinEquiv (.inl (G.numberedBoundaryNext (boundaryOrderIndex u v i)))
    rw [numberedBoundaryNext_index]
    rfl
  | inr x =>
    obtain ⟨i, rfl⟩ := (boundaryOrderIndex v w).surjective x
    change numberedPartialSeam G H 0 (seamOrderIndex u v w (.inr i)) = _
    rw [numberedPartialSeam_index, partialBoundarySwap_zero]
    change seamOrderIndex u v w (.inr (H.boundaryNext i)) =
      finSumFinEquiv (.inr (H.numberedBoundaryNext (boundaryOrderIndex v w i)))
    rw [numberedBoundaryNext_index]
    rfl

theorem numberedPartialSeam_zero_noncrossing (G : PortGraph P u v) (H : PortGraph P v w)
    (hG : G.BoundaryNoncrossing) (hH : H.BoundaryNoncrossing) :
    OrderedNoncrossing (finRotate _) sbtw (numberedPartialSeam G H 0) :=
  orderedNoncrossing_consecutive G.numberedBoundaryNext H.numberedBoundaryNext
    (numberedPartialSeam G H 0) (numberedPartialSeam_zero_index G H)
    (G.numberedBoundaryNext_noncrossing hG) (H.numberedBoundaryNext_noncrossing hH)

/-- All successive seam exchanges preserve the ordered noncrossing
condition on exactly the boundary points that still remain. -/
theorem numberedPartialSeam_noncrossing (G : PortGraph P u v) (H : PortGraph P v w)
    (hG : G.BoundaryNoncrossing) (hH : H.BoundaryNoncrossing) (k : Nat) (hk : k ≤ v.length) :
    OrderedNoncrossing (perm (finRotate _) (numberedSeamRemaining u v w k))
      (fun x y z : Subtype (numberedSeamRemaining u v w k) => sbtw x.val y.val z.val)
      (perm (numberedPartialSeam G H k) (numberedSeamRemaining u v w k)) := by
  induction k with
  | zero => exact (numberedPartialSeam_zero_noncrossing G H hG hH).restrict _
  | succ k ih =>
    have hik : k < v.length := by omega
    let i : Fin v.length := ⟨k, hik⟩
    have hs := OrderedNoncrossing.splice_restrict_nested
      (numberedSeamRemaining u v w k) (numberedSeamRemaining u v w (k + 1))
      (numberedSeamRemaining_mono u v w k) (ih (by omega))
      (retainedSeamLeft u v w i) (retainedSeamRight u v w i)
      (retainedSeam_adjacent u v w i) (retainedSeamLeft_removed u v w i)
      (retainedSeamRight_removed u v w i)
    rw [← numberedPartialSeam_step G H i] at hs
    exact hs

end ThomGame.Pictures.PortGraph
