module

public import ThomGame.Analysis.MatrixStinespring
public import ThomGame.Analysis.MatrixSubalgebraChoi
public import ThomGame.Analysis.MatrixCommutantConvexHull
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Two explicit commuting representations on the Choi dilation space

The first representation acts on the source coordinate. The second acts
on the final Choi coordinate. Coefficients in A give exact A'-equivariance
of the Kraus column.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable (d : Nat)

def matrixChoiCoordinateCycle : (Fin d × (Fin d × Fin d)) ≃ (Fin d × (Fin d × Fin d)) where
  toFun i := (i.2.1, (i.2.2, i.1))
  invFun i := (i.2.2, (i.1, i.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def matrixChoiRightRepresentation :
    CMatrix d →⋆ₐ[ℂ] Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ := by
  let e := matrixChoiCoordinateCycle d
  let r : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
    { Matrix.reindexAlgEquiv ℂ ℂ e with
      map_smul' := fun _ _ => rfl
      map_star' := fun X => (Matrix.conjTranspose_reindex e e X).symm }
  exact r.toStarAlgHom.comp (matrixDiagonalRepresentation (Fin d × Fin d) d)

theorem matrixChoiRightRepresentation_apply (Y : CMatrix d)
    (i j : Fin d × (Fin d × Fin d)) :
    matrixChoiRightRepresentation d Y i j =
      if i.1 = j.1 ∧ i.2.1 = j.2.1 then Y i.2.2 j.2.2 else 0 := by
  change (if (i.1, i.2.1) = (j.1, j.2.1) then Y i.2.2 j.2.2 else 0) = _
  simp only [Prod.mk.injEq]

theorem matrixChoi_representations_commute (X Y : CMatrix d) :
    matrixDiagonalRepresentation (Fin d × Fin d) d X * matrixChoiRightRepresentation d Y =
      matrixChoiRightRepresentation d Y * matrixDiagonalRepresentation (Fin d × Fin d) d X := by
  ext ⟨i, k, r⟩ ⟨j, l, s⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, matrixDiagonalRepresentation_apply,
    matrixChoiRightRepresentation_apply, Prod.mk.injEq]
  simp [ite_and, mul_ite, mul_comm]

variable {d}

theorem matrixChoiRightRepresentation_intertwines
    (A : StarSubalgebra ℂ (CMatrix d))
    (S : CStarMatrix (Fin d) (Fin d) (CMatrix d)) (hS : ∀ i j, S i j ∈ A)
    (Y : CMatrix d) (hY : Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    matrixChoiRightRepresentation d Y * matrixKrausColumn (matrixChoiKraus S) =
      matrixKrausColumn (matrixChoiKraus S) * Y := by
  have hc (i j : Fin d) : Y * S i j = S i j * Y :=
    ((mem_matrixSubalgebraCommutant_iff A Y).mp hY (S i j) (hS i j)).symm
  ext ⟨i, k, r⟩ j
  have he := congrArg (fun Z : CMatrix d => Z r j) (hc k i)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, matrixChoiRightRepresentation_apply,
    matrixKrausColumn, matrixChoiKraus, ite_and, ite_mul] using he

end ThomGame.Analysis
