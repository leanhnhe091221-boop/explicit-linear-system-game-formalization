module

public import ThomGame.Pictures.BoundaryVertical
public import ThomGame.Pictures.BoundaryOrder
public import ThomGame.Pictures.NestedAdjacentDeletion

/-!
# Actual numbered interfaces of vertical composition

The concatenated boundary order is `u, reverse v, v, reverse w`.
After removing the interface indices below `k`, the two occurrences of
index `k` are adjacent in the genuine first-return circle. Partial seam
exchanges are explicit permutations on the actual boundary-index type.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn CycleSurgery

variable {S : Type*} (u v w : List S)

abbrev NumberedSeam := Fin ((u.length + v.length) + (v.length + w.length))

def seamOrderIndex : SeamBoundary u v w ≃ NumberedSeam u v w :=
  (Equiv.sumCongr (boundaryOrderIndex u v) (boundaryOrderIndex v w)).trans finSumFinEquiv

theorem seamOrderIndex_top_val (i : Fin u.length) :
    (seamOrderIndex u v w (.inl (.inl i))).val = i.val := rfl

theorem seamOrderIndex_left_val (i : Fin v.length) :
    (seamOrderIndex u v w (.inl (.inr i))).val = u.length + (v.length - 1 - i.val) := by
  change u.length + i.rev.val = _
  rw [Fin.val_rev]
  omega

theorem seamOrderIndex_right_val (i : Fin v.length) :
    (seamOrderIndex u v w (.inr (.inl i))).val = u.length + v.length + i.val := rfl

theorem seamOrderIndex_bottom_val (i : Fin w.length) :
    (seamOrderIndex u v w (.inr (.inr i))).val =
      u.length + v.length + (v.length + (w.length - 1 - i.val)) := by
  change u.length + v.length + (v.length + i.rev.val) = _
  rw [Fin.val_rev]
  omega

def partialBoundarySwap (k : Nat) : Perm (SeamBoundary u v w) where
  toFun
    | .inl (.inr i) => if i.val < k then .inr (.inl i) else .inl (.inr i)
    | .inr (.inl i) => if i.val < k then .inl (.inr i) else .inr (.inl i)
    | b => b
  invFun
    | .inl (.inr i) => if i.val < k then .inr (.inl i) else .inl (.inr i)
    | .inr (.inl i) => if i.val < k then .inl (.inr i) else .inr (.inl i)
    | b => b
  left_inv b := by
    rcases b with (i | i) | (i | i) <;> first | rfl | (by_cases hi : i.val < k <;> simp [hi])
  right_inv b := by
    rcases b with (i | i) | (i | i) <;> first | rfl | (by_cases hi : i.val < k <;> simp [hi])

theorem partialBoundarySwap_zero : partialBoundarySwap u v w 0 = 1 := by
  ext b
  rcases b with (i | i) | (i | i) <;> simp [partialBoundarySwap]

theorem partialBoundarySwap_all : partialBoundarySwap u v w v.length = boundarySeamSwap := by
  ext b
  rcases b with (i | i) | (i | i) <;> simp [partialBoundarySwap, boundarySeamSwap]

theorem partialBoundarySwap_step (i : Fin v.length) :
    partialBoundarySwap u v w (i.val + 1) =
      swap (.inl (.inr i)) (.inr (.inl i)) * partialBoundarySwap u v w i.val := by
  ext b
  rcases b with (j | j) | (j | j)
  · simp [partialBoundarySwap, swap_apply_def]
  · by_cases hji : j = i
    · subst j
      simp [partialBoundarySwap]
    · have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
      simp only [Perm.mul_apply, partialBoundarySwap, Equiv.coe_fn_mk]
      by_cases hj : j.val < i.val
      · simp [hj, show j.val < i.val + 1 by omega, swap_apply_def, hji]
      · simp [hj, show ¬ j.val < i.val + 1 by omega, swap_apply_def, hji]
  · by_cases hji : j = i
    · subst j
      simp [partialBoundarySwap]
    · have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
      simp only [Perm.mul_apply, partialBoundarySwap, Equiv.coe_fn_mk]
      by_cases hj : j.val < i.val
      · simp [hj, show j.val < i.val + 1 by omega, swap_apply_def, hji]
      · simp [hj, show ¬ j.val < i.val + 1 by omega, swap_apply_def, hji]
  · simp [partialBoundarySwap, swap_apply_def]

def SeamRemaining (k : Nat) : SeamBoundary u v w → Prop
  | .inl (.inr i) => k ≤ i.val
  | .inr (.inl i) => k ≤ i.val
  | _ => True

def numberedSeamRemaining (k : Nat) (x : NumberedSeam u v w) : Prop :=
  SeamRemaining u v w k ((seamOrderIndex u v w).symm x)

theorem numberedSeamRemaining_index (k : Nat) (x : SeamBoundary u v w) :
    numberedSeamRemaining u v w k (seamOrderIndex u v w x) ↔ SeamRemaining u v w k x := by
  simp [numberedSeamRemaining]

theorem numberedSeamRemaining_mono (k : Nat) (x : NumberedSeam u v w)
    (hx : numberedSeamRemaining u v w (k + 1) x) : numberedSeamRemaining u v w k x := by
  obtain ⟨x, rfl⟩ := (seamOrderIndex u v w).surjective x
  rw [numberedSeamRemaining_index] at hx ⊢
  rcases x with (i | i) | (i | i) <;> simp only [SeamRemaining] at hx ⊢ <;> omega

theorem SeamRemaining_all (x : SeamBoundary u v w) :
    SeamRemaining u v w v.length x ↔ IsOuter x := by
  rcases x with (i | i) | (i | i) <;> simp [SeamRemaining, IsOuter, Nat.not_le.mpr i.isLt]

theorem numberedSeamRemaining_iff (k : Nat) (hk : k ≤ v.length) (x : NumberedSeam u v w) :
    numberedSeamRemaining u v w k x ↔
      x.val < u.length + v.length - k ∨ u.length + v.length + k ≤ x.val := by
  obtain ⟨x, rfl⟩ := (seamOrderIndex u v w).surjective x
  rw [numberedSeamRemaining_index]
  rcases x with (i | i) | (i | i)
  all_goals have hi := i.isLt
  · rw [seamOrderIndex_top_val]
    constructor
    · intro _
      left
      omega
    · intro _
      trivial
  · rw [seamOrderIndex_left_val]
    simp only [SeamRemaining]
    omega
  · rw [seamOrderIndex_right_val]
    simp only [SeamRemaining]
    omega
  · rw [seamOrderIndex_bottom_val]
    constructor
    · intro _
      right
      omega
    · intro _
      trivial

def retainedSeamLeft (i : Fin v.length) : Subtype (numberedSeamRemaining u v w i.val) :=
  ⟨seamOrderIndex u v w (.inl (.inr i)), (numberedSeamRemaining_index u v w i.val _).mpr le_rfl⟩

def retainedSeamRight (i : Fin v.length) : Subtype (numberedSeamRemaining u v w i.val) :=
  ⟨seamOrderIndex u v w (.inr (.inl i)), (numberedSeamRemaining_index u v w i.val _).mpr le_rfl⟩

theorem retainedSeamLeft_removed (i : Fin v.length) :
    ¬ numberedSeamRemaining u v w (i.val + 1) (retainedSeamLeft u v w i).val := by
  rw [retainedSeamLeft, numberedSeamRemaining_index]
  exact Nat.not_succ_le_self _

theorem retainedSeamRight_removed (i : Fin v.length) :
    ¬ numberedSeamRemaining u v w (i.val + 1) (retainedSeamRight u v w i).val := by
  rw [retainedSeamRight, numberedSeamRemaining_index]
  exact Nat.not_succ_le_self _

/-- In the actual partially deleted boundary, the next interface pair
is adjacent in the positive first-return circle. -/
theorem retainedSeam_adjacent (i : Fin v.length) :
    perm (finRotate _) (numberedSeamRemaining u v w i.val) (retainedSeamLeft u v w i) =
      retainedSeamRight u v w i := by
  apply Subtype.ext
  apply Eq.symm
  apply eq_perm_of_hit _ _ _ (retainedSeamRight u v w i).property
  have hi := i.isLt
  let : NeZero ((u.length + v.length) + (v.length + w.length)) := ⟨by omega⟩
  apply FinCircle.hit_of_lt
  · change (seamOrderIndex u v w (.inl (.inr i))).val <
      (seamOrderIndex u v w (.inr (.inl i))).val
    rw [seamOrderIndex_left_val, seamOrderIndex_right_val]
    omega
  · intro z haz hzb hz
    change (seamOrderIndex u v w (.inl (.inr i))).val < z.val at haz
    change z.val < (seamOrderIndex u v w (.inr (.inl i))).val at hzb
    rw [seamOrderIndex_left_val] at haz
    rw [seamOrderIndex_right_val] at hzb
    rw [numberedSeamRemaining_iff u v w i.val (by omega)] at hz
    omega

end ThomGame.Pictures.PortGraph
