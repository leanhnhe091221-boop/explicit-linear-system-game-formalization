module

public import ThomGame.Analysis.MatrixALTHighPolarCompletion

/-!
# Recovering corner mass from a scalar error and the trace

The scalar component uses the original ambient normalized trace.
Its exact squared norm is the squared trace modulus divided by the corner trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixProjection_trace_re_pos {P : CMatrix d} (hP : IsStarProjection P) (hne : P ≠ 0) :
    0 < (normalizedTrace P).re := by
  have he := matrixTraceReal_projection_pos (NeZero.pos d) hP hne
  simpa only [matrixTraceReal, normalizedTrace_re] using he

theorem matrixCorner_scalar_norm_sq {P : CMatrix d} (hP : IsStarProjection P) (hne : P ≠ 0)
    (X : CMatrix d) :
    hsNorm ((normalizedTrace X / normalizedTrace P) • P) ^ 2 =
      ‖normalizedTrace X‖ ^ 2 / (normalizedTrace P).re := by
  have hp := matrixProjection_trace_re_pos hP hne
  have ht : ‖normalizedTrace P‖ = (normalizedTrace P).re := by
    rw [← normalizedTrace_selfAdjoint_real hP.isSelfAdjoint, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp, Complex.ofReal_re]
  rw [hsNorm_smul, mul_pow, norm_div, div_pow, hsNorm_projection_sq hP, ht]
  field_simp [hp.ne']

omit [NeZero d] in
theorem hsNorm_add_sq_le_two (X Y : CMatrix d) :
    hsNorm (X + Y) ^ 2 ≤ 2 * hsNorm X ^ 2 + 2 * hsNorm Y ^ 2 := by
  have he := (sq_le_sq₀ (hsNorm_nonneg _) (add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))).mpr
    (hsNorm_add_le X Y)
  nlinarith [sq_nonneg (hsNorm X - hsNorm Y)]

theorem matrixCorner_mass_le_scalar_error {P : CMatrix d} (hP : IsStarProjection P) (hne : P ≠ 0)
    (X : CMatrix d) :
    hsNorm X ^ 2 ≤ 2 * hsNorm (X - (normalizedTrace X / normalizedTrace P) • P) ^ 2 +
      2 * (‖normalizedTrace X‖ ^ 2 / (normalizedTrace P).re) := by
  have he := hsNorm_add_sq_le_two (X - (normalizedTrace X / normalizedTrace P) • P)
    ((normalizedTrace X / normalizedTrace P) • P)
  rw [sub_add_cancel, matrixCorner_scalar_norm_sq hP hne] at he
  exact he

end ThomGame.Analysis
