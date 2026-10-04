module

public import ThomGame.Analysis.MatrixSubalgebraAlgebraicBlocks
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Central orthogonal supports of the algebraic matrix blocks

The coordinate units of the algebraic decomposition pull back to central
idempotents. Centrality makes them normal, so the C-star structure proves
that they are genuine self-adjoint projections in the original matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

noncomputable def matrixAlgebraicBlockSupport (i : Fin S.count) : A :=
  S.equiv.symm (fun j => if i = j then 1 else 0)

theorem matrixAlgebraicBlockSupport_equiv (i j : Fin S.count) :
    S.equiv (matrixAlgebraicBlockSupport A S i) j = if i = j then 1 else 0 := by
  simp [matrixAlgebraicBlockSupport]

theorem matrixAlgebraicBlockSupport_mul_self (i : Fin S.count) :
    matrixAlgebraicBlockSupport A S i * matrixAlgebraicBlockSupport A S i =
      matrixAlgebraicBlockSupport A S i := by
  apply S.equiv.injective
  ext j a b
  simp only [map_mul, Pi.mul_apply, matrixAlgebraicBlockSupport_equiv]
  by_cases h : i = j <;> simp [h]

theorem matrixAlgebraicBlockSupport_commutes (i : Fin S.count) (X : A) :
    matrixAlgebraicBlockSupport A S i * X = X * matrixAlgebraicBlockSupport A S i := by
  apply S.equiv.injective
  ext j a b
  simp only [map_mul, Pi.mul_apply, matrixAlgebraicBlockSupport_equiv]
  by_cases h : i = j <;> simp [h]

theorem matrixAlgebraicBlockSupport_mul_of_ne (i j : Fin S.count) (hij : i ≠ j) :
    matrixAlgebraicBlockSupport A S i * matrixAlgebraicBlockSupport A S j = 0 := by
  apply S.equiv.injective
  ext k a b
  simp only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply, matrixAlgebraicBlockSupport_equiv]
  by_cases hi : i = k
  · have hj : j ≠ k := fun h => hij (hi.trans h.symm)
    simp [hi, hj]
  · simp [hi]

theorem matrixAlgebraicBlockSupport_sum : ∑ i, matrixAlgebraicBlockSupport A S i = 1 := by
  apply S.equiv.injective
  simp only [map_sum, map_one]
  funext j
  simp [matrixAlgebraicBlockSupport_equiv]

theorem matrixAlgebraicBlockSupport_ne_zero (i : Fin S.count) :
    matrixAlgebraicBlockSupport A S i ≠ 0 := by
  let : NeZero (S.size i) := ⟨Nat.ne_of_gt (S.size_pos i)⟩
  intro h
  have he := congrArg (fun X : A => S.equiv X i) h
  have hc : (1 : CMatrix (S.size i)) = 0 := by
    simpa only [matrixAlgebraicBlockSupport_equiv, ite_true, map_zero, Pi.zero_apply] using he
  exact one_ne_zero hc

theorem matrixAlgebraicBlockSupport_projection (i : Fin S.count) :
    IsStarProjection (matrixAlgebraicBlockSupport A S i : CMatrix d) := by
  apply isStarProjection_iff_isIdempotentElem_and_isStarNormal.mpr
  refine ⟨?_, ⟨?_⟩⟩
  · exact congrArg Subtype.val (matrixAlgebraicBlockSupport_mul_self A S i)
  · exact congrArg Subtype.val
      (matrixAlgebraicBlockSupport_commutes A S i (star (matrixAlgebraicBlockSupport A S i))).symm

theorem matrixAlgebraicBlockSupport_star (i : Fin S.count) :
    star (matrixAlgebraicBlockSupport A S i) = matrixAlgebraicBlockSupport A S i := by
  apply Subtype.ext
  exact (matrixAlgebraicBlockSupport_projection A S i).isSelfAdjoint.star_eq

end ThomGame.Analysis
