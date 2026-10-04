module

public import ThomGame.Analysis.MatrixBlockCommutantAverage

/-!
# The finite block average equals the actual trace expectation

Trace cyclicity and the matrix-unit relations give the defining
pairing against every element of the represented commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

theorem matrixBlockUnitSandwich_trace_pairing (i : Fin P.count) (X Y : CMatrix m)
    (hY : ∀ Z : A, ρ Z * Y = Y * ρ Z) :
    (Y * matrixBlockUnitSandwich A P ρ i X).trace =
      (P.size i : ℂ) * ∑ b, (Y * ρ (matrixStarBlockUnit A P i b b) * X).trace := by
  have he (a b : Fin (P.size i)) :
      (Y * (ρ (matrixStarBlockUnit A P i a b) * X * ρ (matrixStarBlockUnit A P i b a))).trace =
        (Y * ρ (matrixStarBlockUnit A P i b b) * X).trace := by
    calc
      _ = (ρ (matrixStarBlockUnit A P i b a) * (Y * ρ (matrixStarBlockUnit A P i a b) * X)).trace := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hY]
        simp only [Matrix.mul_assoc, ← map_mul, matrixAlgebraicBlockUnit_mul_same]
  simp only [matrixBlockUnitSandwich, Matrix.mul_sum, Matrix.trace_sum, he,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem matrixBlockCommutantAverage_trace_pairing (X Y : CMatrix m)
    (hY : ∀ Z : A, ρ Z * Y = Y * ρ Z) :
    (Y * matrixBlockCommutantAverage A P ρ X).trace = (Y * X).trace := by
  simp only [matrixBlockCommutantAverage, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    matrixBlockUnitSandwich_trace_pairing A P ρ _ X Y hY]
  have hc (i : Fin P.count) : (P.size i : ℂ)⁻¹ * (P.size i : ℂ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (P.size_pos i)))
  simp only [← mul_assoc, hc, one_mul]
  simp only [← Matrix.trace_sum]
  congr 1
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum, ← map_sum,
    matrixStarBlockUnit_total_diagonal_sum, map_one, Matrix.mul_one]

variable [NeZero m]

theorem matrixBlockCommutantAverage_eq_expectation (X : CMatrix m) :
    matrixBlockCommutantAverage A P ρ X =
      matrixTraceProjection (StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m))) X := by
  symm
  apply matrixTraceProjection_unique _ X _ (matrixBlockCommutantAverage_mem A P ρ X)
  intro Y hY
  have hs := (mem_matrixSubalgebraCommutant_iff ρ.range (star Y)).mp (star_mem hY)
  have he := matrixBlockCommutantAverage_trace_pairing A P ρ X (star Y)
    (fun Z => hs (ρ Z) ⟨Z, rfl⟩)
  rw [mul_sub, normalizedTrace_sub]
  exact sub_eq_zero.mpr (congrArg (fun z : ℂ => z / m) he.symm)

end ThomGame.Analysis
