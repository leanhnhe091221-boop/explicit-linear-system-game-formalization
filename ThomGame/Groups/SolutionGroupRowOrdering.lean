module

public import ThomGame.Finite.RowOrdering
public import ThomGame.Groups.SolutionTriangle

/-! Row reordering gives an actual solution-group isomorphism fixing every generator. -/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {R C G : Type*} [Group G] {S T : SparseSystem R C}

def Model.permuteRows (M : Model S G) (p : S.RowPermutation T) : Model T G where
  j := M.j
  x := M.x
  j_square := M.j_square
  x_square := M.x_square
  j_commutes := M.j_commutes
  row_commutes r i j := by
    rw [p.column_eq, p.column_eq]
    exact M.row_commutes r _ _
  row_product r := by
    have h := M.row_word_product r _ (p.columns_perm r)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc, p.rhs_eq] using h

def rowPermutationHom (p : S.RowPermutation T) : GroupOf T →* GroupOf S :=
  ((canonicalModel S).permuteRows p).toHom

theorem rowPermutationHom_J (p : S.RowPermutation T) : rowPermutationHom p (J T) = J S :=
  Model.toHom_J _

theorem rowPermutationHom_x (p : S.RowPermutation T) (c : C) :
    rowPermutationHom p (x T c) = x S c := Model.toHom_x _ c

theorem rowPermutationHom_comp (p : S.RowPermutation T) :
    (rowPermutationHom p).comp (rowPermutationHom p.symm) = MonoidHom.id (GroupOf S) := by
  apply hom_ext
  · simp [MonoidHom.comp_apply, rowPermutationHom_J]
  · intro c
    simp [MonoidHom.comp_apply, rowPermutationHom_x]

def rowPermutationEquiv (p : S.RowPermutation T) : GroupOf T ≃* GroupOf S where
  toFun := rowPermutationHom p
  invFun := rowPermutationHom p.symm
  left_inv g := by
    have h : (rowPermutationHom p.symm).comp (rowPermutationHom p) =
        MonoidHom.id (GroupOf T) := by
      apply hom_ext
      · simp [MonoidHom.comp_apply, rowPermutationHom_J]
      · intro c
        simp [MonoidHom.comp_apply, rowPermutationHom_x]
    exact DFunLike.congr_fun h g
  right_inv g := DFunLike.congr_fun (rowPermutationHom_comp p) g
  map_mul' := (rowPermutationHom p).map_mul

theorem rowPermutationEquiv_J (p : S.RowPermutation T) : rowPermutationEquiv p (J T) = J S :=
  rowPermutationHom_J p

theorem rowPermutationEquiv_x (p : S.RowPermutation T) (c : C) :
    rowPermutationEquiv p (x T c) = x S c := rowPermutationHom_x p c

end ThomGame.SolutionGroup
