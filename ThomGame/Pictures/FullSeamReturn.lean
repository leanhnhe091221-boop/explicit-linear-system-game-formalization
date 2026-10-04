module

public import ThomGame.Pictures.FullSeamState

/-!
# First returns of actual partial seam circuits

The retained numerical boundary and the retained full darts are
explicitly equivalent. Their first returns agree because each boundary
step expands to a genuine full-dart path. Internal darts are not deleted
from the full circuit permutation.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}
variable (G : PortGraph P u v) (H : PortGraph P v w)

def fullBoundaryPorts : SeamBoundary u v w ≃
    {a : G.Dart ⊕ H.Dart // Sum.elim G.IsBoundary H.IsBoundary a} :=
  (Equiv.sumCongr G.boundaryPorts H.boundaryPorts).trans
    (Equiv.subtypeSum (p := Sum.elim G.IsBoundary H.IsBoundary)).symm

theorem fullBoundaryPorts_val (b : SeamBoundary u v w) :
    (fullBoundaryPorts G H b).val = oldBoundaryDart G H b := by
  cases b <;> rfl

def remainingBoundaryPorts (k : Nat) : Subtype (SeamRemaining u v w k) ≃
    Subtype (FullSeamRemaining G H k) :=
  (((fullBoundaryPorts G H).subtypeEquiv (fun b =>
    ((fullSeamRemaining_index G H k b).symm.trans
      (by rw [fullBoundaryPorts_val]))))).trans
    (nestedSubset (Sum.elim G.IsBoundary H.IsBoundary) (FullSeamRemaining G H k)
      (fullSeamRemaining_boundary G H k))

theorem remainingBoundaryPorts_val (k : Nat) (b : Subtype (SeamRemaining u v w k)) :
    (remainingBoundaryPorts G H k b).val = oldBoundaryDart G H b.val :=
  fullBoundaryPorts_val G H b.val

theorem remainingBoundaryPorts_eq (k : Nat) (b : Subtype (SeamRemaining u v w k)) :
    remainingBoundaryPorts G H k b =
      ⟨oldBoundaryDart G H b.val, (fullSeamRemaining_index G H k b.val).mpr b.property⟩ :=
  Subtype.ext (remainingBoundaryPorts_val G H k b)

theorem remainingBoundaryPorts_next (k l : Nat) (b : Subtype (SeamRemaining u v w l)) :
    perm (fullPartialSeam G H k) (FullSeamRemaining G H l) (remainingBoundaryPorts G H l b) =
      remainingBoundaryPorts G H l (perm (boundaryPartialSeam G H k) (SeamRemaining u v w l) b) := by
  apply Subtype.ext
  rw [remainingBoundaryPorts_eq, remainingBoundaryPorts_val]
  exact (perm_preserved_of_paths (fullPartialSeam G H k) (FullSeamRemaining G H l)
    (boundaryPartialSeam G H k) (SeamRemaining u v w l) (oldBoundaryDart G H)
    (fun b => (fullPartialSeam_boundary_hit G H k b).weaken (fullSeamRemaining_boundary G H l))
    (fullSeamRemaining_index G H l) b).symm

def numberedBoundaryPorts (k : Nat) : Subtype (numberedSeamRemaining u v w k) ≃
    Subtype (SeamRemaining u v w k) :=
  (seamOrderIndex u v w).symm.subtypeEquiv (fun _ => Iff.rfl)

def numberedFullBoundary (k : Nat) : Subtype (numberedSeamRemaining u v w k) ≃
    Subtype (FullSeamRemaining G H k) :=
  (numberedBoundaryPorts k).trans (remainingBoundaryPorts G H k)

theorem numberedBoundaryPorts_next (k l : Nat) (b : Subtype (numberedSeamRemaining u v w l)) :
    perm (boundaryPartialSeam G H k) (SeamRemaining u v w l) (numberedBoundaryPorts l b) =
      numberedBoundaryPorts l (perm (numberedPartialSeam G H k) (numberedSeamRemaining u v w l) b) := by
  apply perm_subtypeEquiv
  intro x
  apply (seamOrderIndex u v w).injective
  simp only [Equiv.apply_symm_apply]
  exact (numberedPartialSeam_index G H k ((seamOrderIndex u v w).symm x)).symm.trans
    (congrArg (numberedPartialSeam G H k) ((seamOrderIndex u v w).apply_symm_apply x))

theorem numberedFullBoundary_next (k l : Nat) (b : Subtype (numberedSeamRemaining u v w l)) :
    perm (fullPartialSeam G H k) (FullSeamRemaining G H l) (numberedFullBoundary G H l b) =
      numberedFullBoundary G H l (perm (numberedPartialSeam G H k) (numberedSeamRemaining u v w l) b) := by
  change perm _ _ (remainingBoundaryPorts G H l (numberedBoundaryPorts l b)) = _
  rw [remainingBoundaryPorts_next, numberedBoundaryPorts_next]
  rfl

theorem numberedFullBoundary_sameCycle (k l : Nat)
    (a b : Subtype (numberedSeamRemaining u v w l)) :
    (perm (numberedPartialSeam G H k) (numberedSeamRemaining u v w l)).SameCycle a b ↔
      (fullPartialSeam G H k).SameCycle (numberedFullBoundary G H l a).val
        (numberedFullBoundary G H l b).val :=
  (FiniteReturn.sameCycle_congr _ _ (numberedFullBoundary G H l)
    (numberedFullBoundary_next G H k l) a b).trans (sameCycle_iff _ _ _ _)

theorem numberedFullBoundary_left (i : Fin v.length) :
    (numberedFullBoundary G H i.val (retainedSeamLeft u v w i)).val = .inl (.bottom i) := by
  change (remainingBoundaryPorts G H i.val (numberedBoundaryPorts i.val _)).val = _
  rw [remainingBoundaryPorts_val]
  change oldBoundaryDart G H ((seamOrderIndex u v w).symm
    (seamOrderIndex u v w (.inl (.inr i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem numberedFullBoundary_right (i : Fin v.length) :
    (numberedFullBoundary G H i.val (retainedSeamRight u v w i)).val = .inr (.top i) := by
  change (remainingBoundaryPorts G H i.val (numberedBoundaryPorts i.val _)).val = _
  rw [remainingBoundaryPorts_val]
  change oldBoundaryDart G H ((seamOrderIndex u v w).symm
    (seamOrderIndex u v w (.inr (.inl i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end ThomGame.Pictures.PortGraph
