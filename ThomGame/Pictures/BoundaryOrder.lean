module

public import ThomGame.Pictures.CircularInvolutions
public import ThomGame.Pictures.BoundaryReturn

/-!
# The specified circular order of a diagram boundary

The upper ports occur left to right, followed by the lower ports right
to left. This supplies an actual finite circular order, separately from
the graph's boundary-visit permutation. `BoundaryNoncrossing` compares
those two structures; its definition does not presume it holds for all
graphs or all extracted diagrams.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

def boundaryOrderIndex (u v : List S) : BoundaryIndex u v ≃ Fin (u.length + v.length) :=
  (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv

theorem boundaryOrderIndex_top_val (u v : List S) (i : Fin u.length) :
    (boundaryOrderIndex u v (.inl i)).val = i.val := rfl

theorem boundaryOrderIndex_bottom_val (u v : List S) (i : Fin v.length) :
    (boundaryOrderIndex u v (.inr i)).val = u.length + i.rev.val := rfl

def boundaryCyclic (u v : List S) : Equiv.Perm (BoundaryIndex u v) :=
  ((boundaryOrderIndex u v).trans (finRotate _)).trans (boundaryOrderIndex u v).symm

def boundaryBetween (u v : List S) (a b c : BoundaryIndex u v) : Prop :=
  sbtw (boundaryOrderIndex u v a) (boundaryOrderIndex u v b) (boundaryOrderIndex u v c)

def BoundaryNoncrossing (G : PortGraph P u v) : Prop :=
  OrderedNoncrossing (boundaryCyclic u v) (boundaryBetween u v) G.boundaryNext

noncomputable def numberedBoundaryNext (G : PortGraph P u v) : Equiv.Perm (Fin (u.length + v.length)) :=
  ((boundaryOrderIndex u v).symm.trans G.boundaryNext).trans (boundaryOrderIndex u v)

theorem numberedBoundaryNext_index (G : PortGraph P u v) (i : BoundaryIndex u v) :
    G.numberedBoundaryNext (boundaryOrderIndex u v i) =
      boundaryOrderIndex u v (G.boundaryNext i) := by
  change boundaryOrderIndex u v (G.boundaryNext ((boundaryOrderIndex u v).symm
    (boundaryOrderIndex u v i))) = _
  rw [Equiv.symm_apply_apply]

theorem boundaryCyclic_index (i : BoundaryIndex u v) :
    boundaryOrderIndex u v (boundaryCyclic u v i) = finRotate _ (boundaryOrderIndex u v i) := by
  change boundaryOrderIndex u v ((boundaryOrderIndex u v).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem boundaryCyclic_sameCycle (i j : BoundaryIndex u v) :
    (boundaryCyclic u v).SameCycle i j :=
  (FiniteReturn.sameCycle_congr _ _ (boundaryOrderIndex u v)
    (fun a => (boundaryCyclic_index a).symm) i j).mpr (finRotate_sameCycle _ _)

theorem boundaryNoncrossing_of_numbered (G : PortGraph P u v)
    (h : OrderedNoncrossing (finRotate (u.length + v.length)) sbtw G.numberedBoundaryNext) :
    G.BoundaryNoncrossing := by
  apply h.transport (boundaryOrderIndex u v).symm
  · intro a
    simp [boundaryCyclic]
  · intro a
    simp [numberedBoundaryNext]
  · intro a b c
    simp [boundaryBetween]

theorem numberedBoundaryNext_noncrossing (G : PortGraph P u v) (h : G.BoundaryNoncrossing) :
    OrderedNoncrossing (finRotate (u.length + v.length)) sbtw G.numberedBoundaryNext :=
  h.transport (boundaryOrderIndex u v) (fun a => (boundaryCyclic_index a).symm)
    G.numberedBoundaryNext_index (fun _ _ _ => Iff.rfl)

theorem boundaryNoncrossing_no_alternating (G : PortGraph P u v) (h : G.BoundaryNoncrossing)
    {a b c d : BoundaryIndex u v} (habc : boundaryBetween u v a b c)
    (hacd : boundaryBetween u v a c d)
    (hac : G.circuit (G.boundaryDart a) = G.circuit (G.boundaryDart c))
    (hbd : G.circuit (G.boundaryDart b) = G.circuit (G.boundaryDart d)) :
    G.circuit (G.boundaryDart a) = G.circuit (G.boundaryDart b) :=
  (G.boundaryNext_sameCycle_iff a b).mp
    (h.noninterlacing a b c d habc hacd
      ((G.boundaryNext_sameCycle_iff a c).mpr hac) ((G.boundaryNext_sameCycle_iff b d).mpr hbd))

variable (P)

theorem numberedBoundaryNext_identity (w : List S) :
    (identity P w).numberedBoundaryNext = Fin.revPerm := by
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex w w).surjective a
  rw [numberedBoundaryNext_index]
  apply Fin.ext
  cases i with
  | inl i =>
    rw [boundaryNext_identity_top, boundaryOrderIndex_bottom_val]
    simp only [Fin.revPerm_apply, Fin.val_rev, boundaryOrderIndex_top_val]
    have hi := i.isLt
    omega
  | inr i =>
    rw [boundaryNext_identity_bottom, boundaryOrderIndex_top_val]
    simp only [Fin.revPerm_apply, Fin.val_rev, boundaryOrderIndex_bottom_val]
    have hi := i.isLt
    omega

theorem boundaryNoncrossing_identity (w : List S) : (identity P w).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  rw [numberedBoundaryNext_identity]
  exact reflection_orderedNoncrossing _

theorem numberedBoundaryNext_cap (s : S) : (cap P s).numberedBoundaryNext = finRotate 2 := by
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex [s, s] []).surjective a
  rw [numberedBoundaryNext_index]
  cases i with
  | inl i =>
    rw [boundaryNext_cap]
    fin_cases i <;> rfl
  | inr i => exact Fin.elim0 i

theorem boundaryNoncrossing_cap (s : S) : (cap P s).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  rw [numberedBoundaryNext_cap]
  exact rotation_orderedNoncrossing _

theorem numberedBoundaryNext_cup (s : S) : (cup P s).numberedBoundaryNext = finRotate 2 := by
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex [] [s, s]).surjective a
  rw [numberedBoundaryNext_index]
  cases i with
  | inl i => exact Fin.elim0 i
  | inr i =>
    rw [boundaryNext_cup]
    fin_cases i <;> rfl

theorem boundaryNoncrossing_cup (s : S) : (cup P s).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  rw [numberedBoundaryNext_cup]
  exact rotation_orderedNoncrossing _

theorem numberedBoundaryNext_down (r : R) :
    (down P r).numberedBoundaryNext = finRotate ((P.word r).length + 0) := by
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex (P.word r) []).surjective a
  rw [numberedBoundaryNext_index]
  cases i with
  | inl i =>
    rw [boundaryNext_down]
    rfl
  | inr i => exact Fin.elim0 i

theorem boundaryNoncrossing_down (r : R) : (down P r).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  rw [numberedBoundaryNext_down]
  exact rotation_orderedNoncrossing _

theorem rev_finRotate_symm {n : Nat} (i : Fin n) :
    ((finRotate n).symm i).rev = finRotate n i.rev := by
  let : NeZero n := i.neZero
  simp [Fin.rev_sub]

theorem numberedBoundaryNext_up (r : R) :
    (up P r).numberedBoundaryNext = finRotate (0 + (P.word r).length) := by
  apply Equiv.ext
  intro a
  obtain ⟨i, rfl⟩ := (boundaryOrderIndex [] (P.word r)).surjective a
  rw [numberedBoundaryNext_index]
  cases i with
  | inl i => exact Fin.elim0 i
  | inr i =>
    rw [boundaryNext_up]
    change Fin.natAdd 0 (((finRotate _).symm i).rev) = finRotate _ (Fin.natAdd 0 i.rev)
    rw [rev_finRotate_symm]
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def]

theorem boundaryNoncrossing_up (r : R) : (up P r).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  rw [numberedBoundaryNext_up]
  exact rotation_orderedNoncrossing _

end ThomGame.Pictures.PortGraph
