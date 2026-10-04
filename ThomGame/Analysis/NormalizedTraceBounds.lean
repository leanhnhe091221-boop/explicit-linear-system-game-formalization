module

public import ThomGame.Analysis.MatrixOperatorBounds

/-!
# Normalized matrix traces and their dimension-independent bound

Cauchy--Schwarz for the flattened matrix and identity gives the normalized
trace bound by the normalized Hilbert--Schmidt norm. The formulas here use
actual complex matrix traces, including the trace of the positive square.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix WithLp
open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius

variable {d : Nat}

@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : CMatrix d) = 0 := by
  simp [normalizedTrace]

@[simp] theorem normalizedTrace_add (A B : CMatrix d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, add_div]

@[simp] theorem normalizedTrace_sub (A B : CMatrix d) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, sub_div]

@[simp] theorem normalizedTrace_smul (c : ℂ) (A : CMatrix d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, mul_div_assoc]

@[simp] theorem normalizedTrace_star (A : CMatrix d) :
    normalizedTrace (star A) = star (normalizedTrace A) := by
  simp [normalizedTrace, Matrix.star_eq_conjTranspose]

theorem normalizedTrace_mul_comm (A B : CMatrix d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  rw [normalizedTrace, normalizedTrace, Matrix.trace_mul_comm]

theorem normalizedTrace_gram (A : CMatrix d) :
    normalizedTrace (star A * A) = ((hsNorm A ^ 2 : ℝ) : ℂ) := by
  rw [normalizedTrace, Matrix.star_eq_conjTranspose, trace_gram, hsNorm_sq]
  push_cast
  rfl

theorem norm_trace_le_sqrt_dim_mul_frobenius (A : CMatrix d) :
    ‖A.trace‖ ≤ Real.sqrt d * ‖A‖ := by
  classical
  let E : EuclideanSpace ℂ (Fin d × Fin d) := toLp 2 (fun ij => (1 : CMatrix d) ij.1 ij.2)
  let V : EuclideanSpace ℂ (Fin d × Fin d) := toLp 2 (fun ij => A ij.1 ij.2)
  have hi : inner ℂ E V = A.trace := by
    simp [E, V, EuclideanSpace.inner_toLp_toLp, dotProduct,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.trace, Matrix.diag]
  have hE : ‖E‖ = Real.sqrt d := by
    have hentry (i j : Fin d) : ‖(1 : CMatrix d) i j‖ ^ 2 = if i = j then 1 else 0 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    simp only [E, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
    simp_rw [hentry]
    simp
  have hV : ‖V‖ = ‖A‖ := by
    simp only [V, EuclideanSpace.norm_eq, Fintype.sum_prod_type, frobenius_eq_sqrt_entries]
  simpa only [hi, hE, hV] using norm_inner_le_norm (𝕜 := ℂ) E V

theorem norm_normalizedTrace_le_hsNorm [NeZero d] (A : CMatrix d) :
    ‖normalizedTrace A‖ ≤ hsNorm A := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hs := dimension_sqrt_pos (d := d)
  calc
    ‖normalizedTrace A‖ = ‖A.trace‖ / d := by simp [normalizedTrace]
    _ ≤ (Real.sqrt d * ‖A‖) / d :=
      div_le_div_of_nonneg_right (norm_trace_le_sqrt_dim_mul_frobenius A) hd.le
    _ = hsNorm A := by
      unfold hsNorm
      apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hs)).mpr
      calc
        Real.sqrt d * ‖A‖ * Real.sqrt d = ‖A‖ * Real.sqrt d ^ 2 := by ring
        _ = ‖A‖ * d := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]

theorem norm_normalizedTrace_le_matrixOpNorm [NeZero d] (A : CMatrix d) :
    ‖normalizedTrace A‖ ≤ matrixOpNorm A :=
  (norm_normalizedTrace_le_hsNorm A).trans (hsNorm_le_matrixOpNorm A)

end ThomGame.Analysis
