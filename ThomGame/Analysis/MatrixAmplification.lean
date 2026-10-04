module

public import ThomGame.Analysis.MatrixConditionalExpectation
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Concrete matrix amplifications

Block matrices are identified with the actual Fin-indexed matrix algebra.
The normalized trace includes the outer dimension factor explicitly.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable (k d : Nat)

noncomputable def matrixBlockFlatten :
    CStarMatrix (Fin k) (Fin k) (CMatrix d) ≃⋆ₐ[ℂ] CMatrix (k * d) := by
  let e : Matrix (Fin k) (Fin k) (CMatrix d) ≃⋆ₐ[ℂ]
      Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ :=
    { Matrix.compAlgEquiv (Fin k) (Fin d) ℂ ℂ with
      map_smul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
  let r : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ ≃⋆ₐ[ℂ] CMatrix (k * d) :=
    { Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv with
      map_smul' := fun _ _ => rfl
      map_star' := fun X => (Matrix.conjTranspose_reindex finProdFinEquiv finProdFinEquiv X).symm }
  exact CStarMatrix.ofMatrixStarAlgEquiv.symm.trans (e.trans r)

@[simp] theorem matrixBlockFlatten_apply
    (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (i j : Fin k × Fin d) :
    matrixBlockFlatten k d X (finProdFinEquiv i) (finProdFinEquiv j) = X i.1 j.1 i.2 j.2 := by
  change X (finProdFinEquiv.symm (finProdFinEquiv i)).1
    (finProdFinEquiv.symm (finProdFinEquiv j)).1
    (finProdFinEquiv.symm (finProdFinEquiv i)).2
    (finProdFinEquiv.symm (finProdFinEquiv j)).2 = _
  simp only [Equiv.symm_apply_apply]

theorem matrixBlockFlatten_trace (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) :
    Matrix.trace (matrixBlockFlatten k d X) = ∑ i, Matrix.trace (X i i) := by
  unfold Matrix.trace Matrix.diag
  rw [← finProdFinEquiv.sum_comp]
  simp only [matrixBlockFlatten_apply, Fintype.sum_prod_type]

theorem matrixBlockFlatten_normalizedTrace (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) :
    normalizedTrace (matrixBlockFlatten k d X) = (∑ i, normalizedTrace (X i i)) / k := by
  simp only [normalizedTrace, matrixBlockFlatten_trace, Nat.cast_mul, ← Finset.sum_div]
  ring

variable {k d}

def matrixBlockSubalgebra (A : StarSubalgebra ℂ (CMatrix d)) :
    StarSubalgebra ℂ (CStarMatrix (Fin k) (Fin k) (CMatrix d)) where
  carrier := {X | ∀ i j, X i j ∈ A}
  zero_mem' := fun _ _ => A.zero_mem
  add_mem' hX hY i j := A.add_mem (hX i j) (hY i j)
  mul_mem' := by
    intro X Y hX hY i j
    change (∑ l, X i l * Y l j) ∈ A
    exact A.sum_mem (fun l _ => A.mul_mem (hX i l) (hY l j))
  one_mem' := by
    intro i j
    change (if i = j then (1 : CMatrix d) else 0) ∈ A
    split
    · exact A.one_mem
    · exact A.zero_mem
  algebraMap_mem' c := by
    intro i j
    change (if i = j then algebraMap ℂ (CMatrix d) c else 0) ∈ A
    split
    · exact A.algebraMap_mem c
    · exact A.zero_mem
  star_mem' hX i j := A.star_mem' (hX j i)

@[simp] theorem mem_matrixBlockSubalgebra (A : StarSubalgebra ℂ (CMatrix d))
    (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) :
    X ∈ matrixBlockSubalgebra A ↔ ∀ i j, X i j ∈ A := Iff.rfl

noncomputable def matrixAmplifiedSubalgebra (A : StarSubalgebra ℂ (CMatrix d)) :
    StarSubalgebra ℂ (CMatrix (k * d)) :=
  (matrixBlockSubalgebra A).map (matrixBlockFlatten k d).toStarAlgHom

theorem matrixBlockFlatten_mem_amplified (A : StarSubalgebra ℂ (CMatrix d))
    (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (hX : ∀ i j, X i j ∈ A) :
    matrixBlockFlatten k d X ∈ matrixAmplifiedSubalgebra A := ⟨X, hX, rfl⟩

end ThomGame.Analysis
