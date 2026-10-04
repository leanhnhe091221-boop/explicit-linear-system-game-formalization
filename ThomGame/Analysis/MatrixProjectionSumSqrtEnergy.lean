module

public import ThomGame.Analysis.MatrixProjectionRangeColumn

/-!
# Boundary energy of the square root of a projection sum

Araki--Yamagami applied to the actual projection-range column and its
compressed unitaries gives the factor 2 used in ALT Theorem 4.3.
The rectangular norms keep the original ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectHSNorm_rectAbs_commutator_sq_le (r : Nat)
    (U : Matrix.unitaryGroup κ ℂ) (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (U.val * matrixRectAbs X - matrixRectAbs X * U.val) ^ 2 ≤
      2 * rectHSNorm r (V.val * X - X * U.val) ^ 2 := by
  have he := rectHSNorm_rectAbs_sub_sq_le r (V.val * X) (X * U.val)
  rw [matrixRectAbs_unitary_left] at he
  have hid : U.val * (matrixRectAbs X - matrixRectAbs (X * U.val)) =
      U.val * matrixRectAbs X - matrixRectAbs X * U.val := by
    rw [Matrix.mul_sub, ← matrixRectAbs_unitary_right_intertwine]
  rw [← hid, rectHSNorm_unitary_mul]
  exact he

theorem matrixIntertwiningEnergy_rectAbs_le {h : Nat} (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) :
    matrixIntertwiningEnergy r U U (matrixRectAbs X) ≤ 2 * matrixIntertwiningEnergy r U V X := by
  have he := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun j _ => rectHSNorm_rectAbs_commutator_sq_le r (U j) (V j) X)
    (lazyMarkovWeight_nonneg h)
  simpa only [matrixIntertwiningEnergy, ← Finset.mul_sum, mul_left_comm (lazyMarkovWeight h) 2] using he

theorem matrixCoordinateEnergy_projection_sum_sqrt_le {μ : Type*} [Fintype μ] [DecidableEq μ]
    {d h : Nat} (U : Fin h → UnitaryMatrix d) (F : μ → CMatrix d)
    (hF : ∀ i, IsStarProjection (F i)) :
    matrixCoordinateEnergy U (CFC.sqrt (∑ i, F i)) ≤ 2 * ∑ i, matrixCoordinateEnergy U (F i) := by
  have he := matrixIntertwiningEnergy_rectAbs_le d U
    (fun j => matrixProjectionBlockUnitary d hF (U j)) (matrixProjectionColumn hF)
  have hc := matrixProjectionColumn_energy_le d hF U
  rw [matrixRectAbs, matrixProjectionColumn_gram] at he
  simp only [matrixIntertwiningEnergy_eq_coordinate] at he hc
  exact he.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

end ThomGame.Analysis
