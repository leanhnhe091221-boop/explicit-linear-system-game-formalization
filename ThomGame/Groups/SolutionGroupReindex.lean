module

public import ThomGame.Groups.SolutionGroup
public import ThomGame.Finite.Reindex

/-! Renumbering rows and columns gives a solution-group isomorphism preserving J. -/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {R C R' C' : Type*} (S : SparseSystem R C) (rows : R ≃ R') (cols : C ≃ C')

def reindexModel : Model S (GroupOf (S.reindex rows cols)) where
  j := J (S.reindex rows cols)
  x c := x (S.reindex rows cols) (cols c)
  j_square := J_sq (S.reindex rows cols)
  x_square c := x_sq (S.reindex rows cols) (cols c)
  j_commutes c := J_commutes_x (S.reindex rows cols) (cols c)
  row_commutes r i k := by
    simpa only [SparseSystem.reindex_column] using
      SolutionGroup.row_commutes (S.reindex rows cols) (rows r) i k
  row_product r := by
    simpa only [SparseSystem.reindex_column, SparseSystem.reindex_rhs] using
      SolutionGroup.row_product (S.reindex rows cols) (rows r)

def unreindexModel : Model (S.reindex rows cols) (GroupOf S) where
  j := J S
  x c := x S (cols.symm c)
  j_square := J_sq S
  x_square c := x_sq S (cols.symm c)
  j_commutes c := J_commutes_x S (cols.symm c)
  row_commutes r i k := by
    simpa [SparseSystem.reindex] using SolutionGroup.row_commutes S (rows.symm r) i k
  row_product r := by
    change x S (cols.symm (cols (S.column (rows.symm r) 0))) *
      x S (cols.symm (cols (S.column (rows.symm r) 1))) *
      x S (cols.symm (cols (S.column (rows.symm r) 2))) =
        if S.rhs (rows.symm r) = 1 then J S else 1
    simp only [Equiv.symm_apply_apply]
    exact SolutionGroup.row_product S (rows.symm r)

theorem reindexModel_comp :
    (unreindexModel S rows cols).toHom.comp (reindexModel S rows cols).toHom =
      MonoidHom.id (GroupOf S) := by
  apply hom_ext
  · simp [MonoidHom.comp_apply, Model.toHom_J, reindexModel, unreindexModel]
  · intro c
    simp [MonoidHom.comp_apply, Model.toHom_x, reindexModel, unreindexModel]

theorem unreindexModel_comp :
    (reindexModel S rows cols).toHom.comp (unreindexModel S rows cols).toHom =
      MonoidHom.id (GroupOf (S.reindex rows cols)) := by
  apply hom_ext
  · simp [MonoidHom.comp_apply, Model.toHom_J, reindexModel, unreindexModel]
  · intro c
    simp [MonoidHom.comp_apply, Model.toHom_x, reindexModel, unreindexModel]

/-- The source and renumbered solution groups are isomorphic, with the specified
central generators corresponding. -/
def reindexEquiv : GroupOf S ≃* GroupOf (S.reindex rows cols) where
  toFun := (reindexModel S rows cols).toHom
  invFun := (unreindexModel S rows cols).toHom
  left_inv g := DFunLike.congr_fun (reindexModel_comp S rows cols) g
  right_inv g := DFunLike.congr_fun (unreindexModel_comp S rows cols) g
  map_mul' := (reindexModel S rows cols).toHom.map_mul

theorem reindexEquiv_J : reindexEquiv S rows cols (J S) = J (S.reindex rows cols) :=
  (reindexModel S rows cols).toHom_J

theorem reindexEquiv_x (c : C) :
    reindexEquiv S rows cols (x S c) = x (S.reindex rows cols) (cols c) :=
  (reindexModel S rows cols).toHom_x c

end ThomGame.SolutionGroup
