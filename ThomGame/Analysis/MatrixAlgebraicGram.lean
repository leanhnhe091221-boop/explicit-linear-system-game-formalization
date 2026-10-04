module

public import ThomGame.Analysis.MatrixAlgebraicBlockUnits
public import ThomGame.Analysis.MatrixSumGramKernel

/-!
# The actual Gram element of algebraic matrix units

The Gram element is positive definite in the original matrix algebra.
It lies in the original star subalgebra because it is a finite sum of
star-squares of the constructed matrix units.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

abbrev MatrixAlgebraicUnitIndex := Σ i : Fin S.count, Fin (S.size i) × Fin (S.size i)

noncomputable def matrixAlgebraicBlockGram (i : Fin S.count) : A :=
  ∑ a, ∑ b, star (matrixAlgebraicBlockUnit A S i a b) * matrixAlgebraicBlockUnit A S i a b

noncomputable def matrixAlgebraicGram : A := ∑ i, matrixAlgebraicBlockGram A S i

theorem matrixAlgebraicBlockUnit_total_diagonal_sum :
    ∑ i, ∑ a, matrixAlgebraicBlockUnit A S i a a = 1 := by
  simp only [matrixAlgebraicBlockUnit_diagonal_sum, matrixAlgebraicBlockSupport_sum]

theorem matrixAlgebraicGram_star : star (matrixAlgebraicGram A S) = matrixAlgebraicGram A S := by
  simp only [matrixAlgebraicGram, matrixAlgebraicBlockGram, star_sum, star_mul, star_star]

theorem matrixAlgebraicGram_eq_sumGram :
    (matrixAlgebraicGram A S : CMatrix d) =
      matrixSumGram (fun k : MatrixAlgebraicUnitIndex A S =>
        (matrixAlgebraicBlockUnit A S k.1 k.2.1 k.2.2 : CMatrix d)) := by
  change A.subtype (matrixAlgebraicGram A S) = _
  simp only [matrixAlgebraicGram, matrixAlgebraicBlockGram, matrixSumGram,
    map_sum, map_mul, map_star, Fintype.sum_sigma, Fintype.sum_prod_type]
  rfl

theorem matrixAlgebraicBlockUnits_common_kernel (v : Fin d → ℂ)
    (hv : ∀ k : MatrixAlgebraicUnitIndex A S,
      (matrixAlgebraicBlockUnit A S k.1 k.2.1 k.2.2 : CMatrix d) *ᵥ v = 0) : v = 0 := by
  have hsum : ∑ i, ∑ a, (matrixAlgebraicBlockUnit A S i a a : CMatrix d) = 1 := by
    simpa only [map_sum, map_one, StarSubalgebra.subtype_apply] using
      congrArg A.subtype (matrixAlgebraicBlockUnit_total_diagonal_sum A S)
  have hdiag (i : Fin S.count) (a : Fin (S.size i)) :
      (matrixAlgebraicBlockUnit A S i a a : CMatrix d) *ᵥ v = 0 := hv ⟨i, a, a⟩
  calc
    v = (1 : CMatrix d) *ᵥ v := (Matrix.one_mulVec v).symm
    _ = (∑ i, ∑ a, (matrixAlgebraicBlockUnit A S i a a : CMatrix d)) *ᵥ v := by rw [hsum]
    _ = 0 := by simp only [Matrix.sum_mulVec, hdiag, Finset.sum_const_zero]

theorem matrixAlgebraicGram_posDef : (matrixAlgebraicGram A S : CMatrix d).PosDef := by
  rw [matrixAlgebraicGram_eq_sumGram]
  exact matrixSumGram_posDef _ (matrixAlgebraicBlockUnits_common_kernel A S)

theorem matrixAlgebraicGram_isUnit : IsUnit (matrixAlgebraicGram A S : CMatrix d) :=
  (matrixAlgebraicGram_posDef A S).isUnit

end ThomGame.Analysis
