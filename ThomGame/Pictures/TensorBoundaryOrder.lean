module

public import ThomGame.Pictures.BoundaryOrder
public import ThomGame.Pictures.BoundaryComposition
public import ThomGame.Pictures.CircularCombination

/-!
# Horizontal composition preserves the noncrossing boundary condition

In the numbered outer boundary the right diagram occupies one interval.
The left diagram occupies its complement, with one gap inserted into its
numbering. Both inclusions are increasing; the two images cannot alternate.
These facts are proved from the actual boundary-index formulas.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w z : List S}

def tensorBoundaryEquiv (u v w z : List S) :
    BoundaryIndex u v ⊕ BoundaryIndex w z ≃ BoundaryIndex (u ++ w) (v ++ z) where
  toFun := Sum.elim tensorBoundaryLeft tensorBoundaryRight
  invFun
    | .inl i => Sum.elim (fun k => .inl (.inl k)) (fun k => .inr (.inl k)) ((appendIndex u w).symm i)
    | .inr i => Sum.elim (fun k => .inl (.inr k)) (fun k => .inr (.inr k)) ((appendIndex v z).symm i)
  left_inv i := by
    rcases i with (i | i) | (i | i) <;> simp [tensorBoundaryLeft, tensorBoundaryRight]
  right_inv i := by
    cases i with
    | inl i =>
      obtain ⟨a, rfl⟩ := (appendIndex u w).surjective i
      cases a <;> simp [tensorBoundaryLeft, tensorBoundaryRight]
    | inr i =>
      obtain ⟨a, rfl⟩ := (appendIndex v z).surjective i
      cases a <;> simp [tensorBoundaryLeft, tensorBoundaryRight]

def numberedTensorIndex (u v w z : List S) :
    Fin (u.length + v.length) ⊕ Fin (w.length + z.length) ≃
      Fin ((u ++ w).length + (v ++ z).length) :=
  ((Equiv.sumCongr (boundaryOrderIndex u v).symm (boundaryOrderIndex w z).symm).trans
    (tensorBoundaryEquiv u v w z)).trans (boundaryOrderIndex (u ++ w) (v ++ z))

theorem numberedTensorIndex_left (i : BoundaryIndex u v) :
    numberedTensorIndex u v w z (.inl (boundaryOrderIndex u v i)) =
      boundaryOrderIndex (u ++ w) (v ++ z) (tensorBoundaryLeft i) := by
  simp [numberedTensorIndex, tensorBoundaryEquiv]

theorem numberedTensorIndex_right (i : BoundaryIndex w z) :
    numberedTensorIndex u v w z (.inr (boundaryOrderIndex w z i)) =
      boundaryOrderIndex (u ++ w) (v ++ z) (tensorBoundaryRight i) := by
  simp [numberedTensorIndex, tensorBoundaryEquiv]

theorem appendIndex_inl_val (a b : List S) (i : Fin a.length) :
    (appendIndex a b (.inl i)).val = i.val := rfl

theorem appendIndex_inr_val (a b : List S) (i : Fin b.length) :
    (appendIndex a b (.inr i)).val = a.length + i.val := rfl

theorem numberedTensorIndex_left_val (i : Fin (u.length + v.length)) :
    (numberedTensorIndex u v w z (.inl i)).val =
      if i.val < u.length then i.val else i.val + (w.length + z.length) := by
  obtain ⟨a, rfl⟩ := (boundaryOrderIndex u v).surjective i
  rw [numberedTensorIndex_left]
  cases a with
  | inl a =>
    simp only [tensorBoundaryLeft, boundaryOrderIndex_top_val, appendIndex_inl_val]
    exact (ite_eq_left a.isLt).symm
  | inr a =>
    have hn : ¬ (boundaryOrderIndex u v (.inr a)).val < u.length := by
      rw [boundaryOrderIndex_bottom_val]
      omega
    rw [ite_eq_right hn]
    simp only [tensorBoundaryLeft, boundaryOrderIndex_bottom_val, List.length_append,
      Fin.val_rev, appendIndex_inl_val]
    have ha := a.isLt
    omega

theorem numberedTensorIndex_right_val (i : Fin (w.length + z.length)) :
    (numberedTensorIndex u v w z (.inr i)).val = u.length + i.val := by
  obtain ⟨a, rfl⟩ := (boundaryOrderIndex w z).surjective i
  rw [numberedTensorIndex_right]
  cases a with
  | inl a =>
    simp only [tensorBoundaryRight, boundaryOrderIndex_top_val, appendIndex_inr_val]
  | inr a =>
    simp only [tensorBoundaryRight, boundaryOrderIndex_bottom_val, List.length_append,
      Fin.val_rev, appendIndex_inr_val]
    have ha := a.isLt
    omega

theorem numberedTensorIndex_left_strictMono :
    StrictMono (fun i : Fin (u.length + v.length) => numberedTensorIndex u v w z (.inl i)) := by
  intro i j hij
  change i.val < j.val at hij
  change (numberedTensorIndex u v w z (.inl i)).val < (numberedTensorIndex u v w z (.inl j)).val
  rw [numberedTensorIndex_left_val, numberedTensorIndex_left_val]
  split_ifs <;> omega

theorem numberedTensorIndex_right_strictMono :
    StrictMono (fun i : Fin (w.length + z.length) => numberedTensorIndex u v w z (.inr i)) := by
  intro i j hij
  change i.val < j.val at hij
  change (numberedTensorIndex u v w z (.inr i)).val < (numberedTensorIndex u v w z (.inr j)).val
  rw [numberedTensorIndex_right_val, numberedTensorIndex_right_val]
  omega

theorem numberedTensorIndex_not_alternating_left
    (a c : Fin (u.length + v.length)) (b d : Fin (w.length + z.length)) :
    ¬ (sbtw (numberedTensorIndex u v w z (.inl a)) (numberedTensorIndex u v w z (.inr b))
          (numberedTensorIndex u v w z (.inl c)) ∧
       sbtw (numberedTensorIndex u v w z (.inl a)) (numberedTensorIndex u v w z (.inl c))
          (numberedTensorIndex u v w z (.inr d))) := by
  rintro ⟨h1, h2⟩
  simp only [Fin.sbtw_iff, Fin.lt_def, numberedTensorIndex_left_val, numberedTensorIndex_right_val] at h1 h2
  have hb := b.isLt
  have hd := d.isLt
  by_cases ha : a.val < u.length <;> by_cases hc : c.val < u.length <;>
    simp only [ha, hc, ite_true, ite_false] at h1 h2 <;> omega

theorem numberedTensorIndex_not_alternating_right
    (a c : Fin (w.length + z.length)) (b d : Fin (u.length + v.length)) :
    ¬ (sbtw (numberedTensorIndex u v w z (.inr a)) (numberedTensorIndex u v w z (.inl b))
          (numberedTensorIndex u v w z (.inr c)) ∧
       sbtw (numberedTensorIndex u v w z (.inr a)) (numberedTensorIndex u v w z (.inr c))
          (numberedTensorIndex u v w z (.inl d))) := by
  rintro ⟨h1, h2⟩
  simp only [Fin.sbtw_iff, Fin.lt_def, numberedTensorIndex_left_val, numberedTensorIndex_right_val] at h1 h2
  have ha := a.isLt
  have hc := c.isLt
  by_cases hb : b.val < u.length <;> by_cases hd : d.val < u.length <;>
    simp only [hb, hd, ite_true, ite_false] at h1 h2 <;> omega

theorem numberedBoundaryNext_tensor_index (G : PortGraph P u v) (H : PortGraph P w z)
    (a : Fin (u.length + v.length) ⊕ Fin (w.length + z.length)) :
    (G.tensor H).numberedBoundaryNext (numberedTensorIndex u v w z a) =
      numberedTensorIndex u v w z (Equiv.sumCongr G.numberedBoundaryNext H.numberedBoundaryNext a) := by
  cases a with
  | inl a =>
    obtain ⟨i, rfl⟩ := (boundaryOrderIndex u v).surjective a
    change (G.tensor H).numberedBoundaryNext (numberedTensorIndex u v w z (.inl (boundaryOrderIndex u v i))) =
      numberedTensorIndex u v w z (.inl (G.numberedBoundaryNext (boundaryOrderIndex u v i)))
    rw [numberedTensorIndex_left, numberedBoundaryNext_index, boundaryNext_tensor_left,
      numberedBoundaryNext_index, numberedTensorIndex_left]
  | inr a =>
    obtain ⟨i, rfl⟩ := (boundaryOrderIndex w z).surjective a
    change (G.tensor H).numberedBoundaryNext (numberedTensorIndex u v w z (.inr (boundaryOrderIndex w z i))) =
      numberedTensorIndex u v w z (.inr (H.numberedBoundaryNext (boundaryOrderIndex w z i)))
    rw [numberedTensorIndex_right, numberedBoundaryNext_index, boundaryNext_tensor_right,
      numberedBoundaryNext_index, numberedTensorIndex_right]

/-- The actual horizontal composition preserves both orbit direction and
noninterlacing in the specified outer-boundary numbering. -/
theorem boundaryNoncrossing_tensor (G : PortGraph P u v) (H : PortGraph P w z)
    (hG : G.BoundaryNoncrossing) (hH : H.BoundaryNoncrossing) : (G.tensor H).BoundaryNoncrossing := by
  apply boundaryNoncrossing_of_numbered
  exact CircularPartition.orderedNoncrossing_combine G.numberedBoundaryNext H.numberedBoundaryNext
    (G.tensor H).numberedBoundaryNext (numberedTensorIndex u v w z)
    (numberedBoundaryNext_tensor_index G H) numberedTensorIndex_left_strictMono
    numberedTensorIndex_right_strictMono numberedTensorIndex_not_alternating_left
    numberedTensorIndex_not_alternating_right (G.numberedBoundaryNext_noncrossing hG)
    (H.numberedBoundaryNext_noncrossing hH)

end ThomGame.Pictures.PortGraph
