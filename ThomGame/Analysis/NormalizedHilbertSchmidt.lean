module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The dimension-normalized Hilbert--Schmidt norm of complex matrices

The normalization is by the full matrix dimension. The entrywise formula
and the normalized trace of A* A are proved equal to this norm, which is
defined from the established Frobenius norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius ComplexConjugate

abbrev CMatrix (d : Nat) := Matrix (Fin d) (Fin d) ℂ
abbrev UnitaryMatrix (d : Nat) := Matrix.unitaryGroup (Fin d) ℂ

noncomputable def normalizedTrace {d : Nat} (A : CMatrix d) : ℂ := A.trace / d

noncomputable def hsNorm {d : Nat} (A : CMatrix d) : ℝ := ‖A‖ / Real.sqrt d

variable {d : Nat}

theorem hsNorm_nonneg (A : CMatrix d) : 0 ≤ hsNorm A := by
  exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

@[simp] theorem hsNorm_zero : hsNorm (0 : CMatrix d) = 0 := by
  simp [hsNorm]

@[simp] theorem hsNorm_neg (A : CMatrix d) : hsNorm (-A) = hsNorm A := by
  simp [hsNorm]

theorem hsNorm_add_le (A B : CMatrix d) : hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  unfold hsNorm
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)

theorem hsNorm_sub_comm (A B : CMatrix d) : hsNorm (A - B) = hsNorm (B - A) := by
  exact congrArg (fun x : ℝ => x / Real.sqrt d) (norm_sub_rev A B)

@[simp] theorem hsNorm_smul (c : ℂ) (A : CMatrix d) : hsNorm (c • A) = ‖c‖ * hsNorm A := by
  simp only [hsNorm, norm_smul, mul_div_assoc]

@[simp] theorem hsNorm_conjTranspose (A : CMatrix d) : hsNorm Aᴴ = hsNorm A := by
  simp only [hsNorm, Matrix.frobenius_norm_conjTranspose]

theorem frobenius_eq_sqrt_entries (A : CMatrix d) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]

theorem hsNorm_eq_sqrt_entries (A : CMatrix d) :
    hsNorm A = Real.sqrt ((∑ i, ∑ j, ‖A i j‖ ^ 2) / d) := by
  rw [hsNorm, frobenius_eq_sqrt_entries, Real.sqrt_div
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]

theorem trace_gram (A : CMatrix d) :
    (Aᴴ * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_comm

theorem trace_gram_re (A : CMatrix d) :
    (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [trace_gram, Complex.ofReal_re]

theorem normalizedTrace_re (A : CMatrix d) :
    (normalizedTrace A).re = A.trace.re / d := by
  change (A.trace / ((d : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]

theorem hsNorm_eq_sqrt_trace (A : CMatrix d) :
    hsNorm A = Real.sqrt (normalizedTrace (Aᴴ * A)).re := by
  rw [normalizedTrace_re, trace_gram_re, hsNorm_eq_sqrt_entries]

variable [NeZero d]

theorem dimension_sqrt_pos : 0 < Real.sqrt (d : ℝ) := by
  exact Real.sqrt_pos.2 (Nat.cast_pos.2 (NeZero.pos d))

@[simp] theorem hsNorm_eq_zero_iff (A : CMatrix d) : hsNorm A = 0 ↔ A = 0 := by
  rw [hsNorm, div_eq_zero_iff]
  simp only [ne_of_gt (dimension_sqrt_pos (d := d)), or_false, norm_eq_zero]

@[simp] theorem hsNorm_sub_eq_zero_iff (A B : CMatrix d) : hsNorm (A - B) = 0 ↔ A = B := by
  rw [hsNorm_eq_zero_iff, sub_eq_zero]

@[simp] theorem normalizedTrace_one : normalizedTrace (1 : CMatrix d) = 1 := by
  simp [normalizedTrace, Matrix.trace_one, NeZero.ne d]

@[simp] theorem hsNorm_one : hsNorm (1 : CMatrix d) = 1 := by
  rw [hsNorm_eq_sqrt_trace]
  simp

omit [NeZero d] in
theorem hsNorm_sq (A : CMatrix d) :
    hsNorm A ^ 2 = (∑ i, ∑ j, ‖A i j‖ ^ 2) / d := by
  rw [hsNorm_eq_sqrt_entries, Real.sq_sqrt]
  exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (Nat.cast_nonneg _)

end ThomGame.Analysis
