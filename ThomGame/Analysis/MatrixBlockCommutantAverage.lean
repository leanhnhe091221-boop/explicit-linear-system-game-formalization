module

public import ThomGame.Analysis.MatrixStarBlockAction
public import ThomGame.Analysis.MatrixCommutantConvexHull

/-!
# A finite matrix-unit average into the actual commutant

For each simple block the average sums all matrix-unit sandwiches
and divides by the block size. Its image commutes with the represented
algebra, including when the representation is not faithful.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

noncomputable def matrixBlockUnitSandwich (i : Fin P.count) (X : CMatrix m) : CMatrix m :=
  ∑ a, ∑ b, ρ (matrixStarBlockUnit A P i a b) * X * ρ (matrixStarBlockUnit A P i b a)

theorem matrixBlockUnitSandwich_mul_left (i : Fin P.count) (c f : Fin (P.size i)) (X : CMatrix m) :
    ρ (matrixStarBlockUnit A P i c f) * matrixBlockUnitSandwich A P ρ i X =
      ∑ b, ρ (matrixStarBlockUnit A P i c b) * X * ρ (matrixStarBlockUnit A P i b f) := by
  classical
  simp only [matrixBlockUnitSandwich, Matrix.mul_sum, ← Matrix.mul_assoc, ← map_mul,
    matrixStarBlockUnit_mul, apply_ite ρ, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem matrixBlockUnitSandwich_mul_right (i : Fin P.count) (c f : Fin (P.size i)) (X : CMatrix m) :
    matrixBlockUnitSandwich A P ρ i X * ρ (matrixStarBlockUnit A P i c f) =
      ∑ b, ρ (matrixStarBlockUnit A P i c b) * X * ρ (matrixStarBlockUnit A P i b f) := by
  classical
  simp only [matrixBlockUnitSandwich, Matrix.sum_mul, Matrix.mul_assoc, ← map_mul,
    matrixStarBlockUnit_mul, apply_ite ρ, map_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem matrixBlockUnitSandwich_mul_left_other (i j : Fin P.count) (hij : i ≠ j)
    (c f : Fin (P.size i)) (X : CMatrix m) :
    ρ (matrixStarBlockUnit A P i c f) * matrixBlockUnitSandwich A P ρ j X = 0 := by
  simp only [matrixBlockUnitSandwich, Matrix.mul_sum, ← Matrix.mul_assoc, ← map_mul,
    matrixStarBlockUnit_mul_other A P i j hij, map_zero, zero_mul, Finset.sum_const_zero]

theorem matrixBlockUnitSandwich_mul_right_other (i j : Fin P.count) (hij : i ≠ j)
    (c f : Fin (P.size i)) (X : CMatrix m) :
    matrixBlockUnitSandwich A P ρ j X * ρ (matrixStarBlockUnit A P i c f) = 0 := by
  simp only [matrixBlockUnitSandwich, Matrix.sum_mul, Matrix.mul_assoc, ← map_mul,
    matrixStarBlockUnit_mul_other A P j i (Ne.symm hij), map_zero, mul_zero, Finset.sum_const_zero]

noncomputable def matrixBlockCommutantAverage (X : CMatrix m) : CMatrix m :=
  ∑ i, ((P.size i : ℂ)⁻¹) • matrixBlockUnitSandwich A P ρ i X

theorem matrixBlockCommutantAverage_commutes_unit (i : Fin P.count) (a b : Fin (P.size i))
    (X : CMatrix m) :
    ρ (matrixStarBlockUnit A P i a b) * matrixBlockCommutantAverage A P ρ X =
      matrixBlockCommutantAverage A P ρ X * ρ (matrixStarBlockUnit A P i a b) := by
  classical
  simp only [matrixBlockCommutantAverage, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [matrixBlockUnitSandwich_mul_left, matrixBlockUnitSandwich_mul_right]
  · rw [matrixBlockUnitSandwich_mul_left_other A P ρ i j hij,
      matrixBlockUnitSandwich_mul_right_other A P ρ i j hij]

theorem matrixBlockCommutantAverage_commutes (Y : A) (X : CMatrix m) :
    ρ Y * matrixBlockCommutantAverage A P ρ X = matrixBlockCommutantAverage A P ρ X * ρ Y := by
  have he : Y = ∑ i, ∑ a, ∑ b, P.equiv Y i a b • matrixStarBlockUnit A P i a b := by
    exact (P.equiv.symm_apply_apply Y).symm.trans
      (matrixAlgebraicBlocks_symm_expansion A P.toAlgebraic (P.equiv Y))
  rw [he]
  simp only [map_sum, map_smul, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    matrixBlockCommutantAverage_commutes_unit]

theorem matrixBlockCommutantAverage_mem (X : CMatrix m) :
    matrixBlockCommutantAverage A P ρ X ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) := by
  apply (mem_matrixSubalgebraCommutant_iff ρ.range _).mpr
  rintro _ ⟨Y, rfl⟩
  exact matrixBlockCommutantAverage_commutes A P ρ Y X

end ThomGame.Analysis
