module

public import ThomGame.Analysis.MatrixMarkovPoincare
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Boundary energy in a spectral basis

Unitary changes of basis preserve the actual normalized commutator
energy. On real diagonal matrices, energy is a weighted sum of squared
entry differences. The weights have their exact row and column masses.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixUnitaryConjugation_mul (V : UnitaryMatrix d) (X Y : CMatrix d) :
    matrixUnitaryConjugation V (X * Y) = matrixUnitaryConjugation V X * matrixUnitaryConjugation V Y :=
  (Unitary.conjStarAlgAut ℂ (CMatrix d) V).map_mul X Y

theorem matrixConjugateUnitary_val (V U : UnitaryMatrix d) :
    (V * U * V⁻¹).val = matrixUnitaryConjugation V U.val := rfl

theorem matrixCoordinateEnergy_conjugate (V : UnitaryMatrix d) (U : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy (fun j => V * U j * V⁻¹) (matrixUnitaryConjugation V X) = matrixCoordinateEnergy U X := by
  simp only [matrixCoordinateEnergy, matrixConjugateUnitary_val, ← matrixUnitaryConjugation_mul,
    ← map_sub, matrixUnitaryConjugation_hsNorm]

theorem matrixUnitary_row_norm_sq_sum (V : UnitaryMatrix d) (i : Fin d) :
    ∑ j, ‖V.val i j‖ ^ 2 = 1 := by
  have he := congrArg (fun X : CMatrix d => (X i i).re) V.prop.2
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re] at he
  rw [Complex.re_sum] at he
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using he

theorem matrixUnitary_col_norm_sq_sum (V : UnitaryMatrix d) (j : Fin d) :
    ∑ i, ‖V.val i j‖ ^ 2 = 1 := by
  have he := congrArg (fun X : CMatrix d => (X j j).re) V.prop.1
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re] at he
  rw [Complex.re_sum] at he
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using he

noncomputable def matrixEnergyWeight (U : Fin h → UnitaryMatrix d) (i j : Fin d) : ℝ :=
  lazyMarkovWeight h / d * ∑ r, ‖(U r).val i j‖ ^ 2

theorem matrixEnergyWeight_nonneg (U : Fin h → UnitaryMatrix d) (i j : Fin d) :
    0 ≤ matrixEnergyWeight U i j :=
  mul_nonneg (div_nonneg (lazyMarkovWeight_nonneg h) (Nat.cast_nonneg d))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem matrix_diagonal_commutator_entry (V : CMatrix d) (e : Fin d → ℝ) (i j : Fin d) :
    ‖(V * Matrix.diagonal (fun i => (e i : ℂ)) - Matrix.diagonal (fun i => (e i : ℂ)) * V) i j‖ ^ 2 =
      ‖V i j‖ ^ 2 * (e j - e i) ^ 2 := by
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have he : V i j * (e j : ℂ) - (e i : ℂ) * V i j = V i j * ((e j : ℂ) - e i) := by ring
  rw [he, norm_mul, mul_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem matrixCoordinateEnergy_diagonal (U : Fin h → UnitaryMatrix d) (e : Fin d → ℝ) :
    matrixCoordinateEnergy U (Matrix.diagonal (fun i => (e i : ℂ))) =
      ∑ i, ∑ j, matrixEnergyWeight U i j * (e j - e i) ^ 2 := by
  simp only [matrixCoordinateEnergy, hsNorm_sq, matrix_diagonal_commutator_entry,
    matrixEnergyWeight]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  ring

variable [NeZero h]

theorem matrixEnergyWeight_row_sum (U : Fin h → UnitaryMatrix d) (i : Fin d) :
    ∑ j, matrixEnergyWeight U i j = (4 * (d : ℝ))⁻¹ := by
  simp only [matrixEnergyWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [matrixUnitary_row_norm_sq_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold lazyMarkovWeight
  have hh : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  field_simp

theorem matrixEnergyWeight_col_sum (U : Fin h → UnitaryMatrix d) (j : Fin d) :
    ∑ i, matrixEnergyWeight U i j = (4 * (d : ℝ))⁻¹ := by
  simp only [matrixEnergyWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [matrixUnitary_col_norm_sq_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold lazyMarkovWeight
  have hh : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  field_simp

variable [NeZero d]

theorem matrixEnergyWeight_total (U : Fin h → UnitaryMatrix d) :
    ∑ i, ∑ j, matrixEnergyWeight U i j = (1 / 4 : ℝ) := by
  simp only [matrixEnergyWeight_row_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

end ThomGame.Analysis
