module

public import ThomGame.Analysis.NormalizedHilbertSchmidt

/-!
# Rectangular Hilbert--Schmidt norms with a fixed normalization

The denominator is an explicit natural number, independent of the
row and column index types. This preserves the original matrix
normalization when passing to rectangular maps and auxiliary sums.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius ComplexConjugate

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

noncomputable def rectHSNorm (r : Nat) (A : Matrix ι κ ℂ) : ℝ := ‖A‖ / Real.sqrt r

theorem rectHSNorm_nonneg (r : Nat) (A : Matrix ι κ ℂ) : 0 ≤ rectHSNorm r A :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

@[simp] theorem rectHSNorm_zero (r : Nat) : rectHSNorm r (0 : Matrix ι κ ℂ) = 0 := by
  simp [rectHSNorm]

theorem rectHSNorm_add_le (r : Nat) (A B : Matrix ι κ ℂ) :
    rectHSNorm r (A + B) ≤ rectHSNorm r A + rectHSNorm r B := by
  unfold rectHSNorm
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)

theorem rectHSNorm_sub_comm (r : Nat) (A B : Matrix ι κ ℂ) :
    rectHSNorm r (A - B) = rectHSNorm r (B - A) := by
  simp only [rectHSNorm, norm_sub_rev A B]

@[simp] theorem rectHSNorm_smul (r : Nat) (c : ℂ) (A : Matrix ι κ ℂ) :
    rectHSNorm r (c • A) = ‖c‖ * rectHSNorm r A := by
  simp only [rectHSNorm, norm_smul, mul_div_assoc]

@[simp] theorem rectHSNorm_conjTranspose (r : Nat) (A : Matrix ι κ ℂ) :
    rectHSNorm r Aᴴ = rectHSNorm r A := by
  simp only [rectHSNorm, Matrix.frobenius_norm_conjTranspose]

theorem rectHSNorm_sq (r : Nat) (A : Matrix ι κ ℂ) :
    rectHSNorm r A ^ 2 = (∑ i, ∑ j, ‖A i j‖ ^ 2) / r := by
  have hn : ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
  have hs : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [rectHSNorm, hn, div_pow, Real.sq_sqrt hs, Real.sq_sqrt (Nat.cast_nonneg r)]

theorem rectangular_trace_gram (A : Matrix ι κ ℂ) :
    (Aᴴ * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_comm

theorem rectHSNorm_eq_sqrt_gram (r : Nat) (A : Matrix ι κ ℂ) :
    rectHSNorm r A = Real.sqrt ((Aᴴ * A).trace.re / r) := by
  rw [rectangular_trace_gram, Complex.ofReal_re, ← rectHSNorm_sq]
  exact (Real.sqrt_sq (rectHSNorm_nonneg r A)).symm

theorem rectHSNorm_unitary_mul [DecidableEq ι] (r : Nat) (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι κ ℂ) : rectHSNorm r (U.val * A) = rectHSNorm r A := by
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  have he : (U.val * A)ᴴ * (U.val * A) = Aᴴ * A := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U.valᴴ U.val A,
      hU, Matrix.one_mul]
  rw [rectHSNorm_eq_sqrt_gram, he, ← rectHSNorm_eq_sqrt_gram]

theorem rectHSNorm_mul_unitary [DecidableEq κ] (r : Nat) (A : Matrix ι κ ℂ)
    (U : Matrix.unitaryGroup κ ℂ) : rectHSNorm r (A * U.val) = rectHSNorm r A := by
  rw [← rectHSNorm_conjTranspose r (A * U.val), conjTranspose_mul]
  change rectHSNorm r ((U⁻¹).val * Aᴴ) = _
  rw [rectHSNorm_unitary_mul, rectHSNorm_conjTranspose]

theorem rectHSNorm_two_unitaries [DecidableEq ι] [DecidableEq κ] (r : Nat)
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) (A : Matrix ι κ ℂ) :
    rectHSNorm r (U.val * A * V.val) = rectHSNorm r A := by
  rw [rectHSNorm_mul_unitary, rectHSNorm_unitary_mul]

theorem rectHSNorm_eq_hsNorm {d : Nat} (A : CMatrix d) : rectHSNorm d A = hsNorm A := rfl

theorem rectHSNorm_eq_zero_iff {r : Nat} (hr : 0 < r) (A : Matrix ι κ ℂ) :
    rectHSNorm r A = 0 ↔ A = 0 := by
  rw [rectHSNorm, div_eq_zero_iff]
  simp only [Real.sqrt_eq_zero', Nat.cast_nonpos, norm_eq_zero]
  simp [Nat.ne_of_gt hr]

end ThomGame.Analysis
