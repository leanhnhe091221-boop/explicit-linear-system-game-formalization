module

public import ThomGame.Analysis.MatrixSpectralCut

/-!
# Distances to matrix projections

Squared Hilbert--Schmidt distance has an exact trace expansion.
In a diagonal basis its contribution at each coordinate depends only
on the diagonal entry of the comparison projection; commutation is
not required. Projection trace difference is bounded by squared distance.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {X Y P Q : CMatrix d}

theorem hsNorm_sub_sq_selfAdjoint (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    hsNorm (X - Y) ^ 2 = (normalizedTrace (X * X)).re -
      2 * (normalizedTrace (X * Y)).re + (normalizedTrace (Y * Y)).re := by
  have he := congrArg Complex.re (normalizedTrace_gram (X - Y))
  simp only [star_sub, hX.star_eq, hY.star_eq, sub_mul, mul_sub, normalizedTrace_sub,
    Complex.sub_re, Complex.ofReal_re, normalizedTrace_mul_comm Y X] at he
  linarith

theorem hsNorm_projection_sq (hP : IsStarProjection P) : hsNorm P ^ 2 = (normalizedTrace P).re := by
  have he := congrArg Complex.re (normalizedTrace_gram P)
  simpa only [hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq, Complex.ofReal_re] using he.symm

theorem matrixProjection_diagonal_bounds (hP : IsStarProjection P) (i : Fin d) :
    0 ≤ (P i i).re ∧ (P i i).re ≤ 1 := by
  have h₀ := (Matrix.nonneg_iff_posSemidef.mp hP.nonneg).diag_nonneg (i := i)
  have h₁ := (Matrix.nonneg_iff_posSemidef.mp hP.one_sub_nonneg).diag_nonneg (i := i)
  refine ⟨(Complex.nonneg_iff.mp h₀).1, ?_⟩
  have h₁' := (Complex.nonneg_iff.mp h₁).1
  simpa only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re, sub_nonneg] using h₁'

theorem normalizedTrace_diagonal_mul_real (e : Fin d → ℝ) (P : CMatrix d) :
    (normalizedTrace (Matrix.diagonal (fun i => (e i : ℂ)) * P)).re =
      (∑ i, e i * (P i i).re) / d := by
  simp only [normalizedTrace_re, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem hsNorm_diagonal_sub_projection_sq (e : Fin d → ℝ) (hP : IsStarProjection P) :
    hsNorm (Matrix.diagonal (fun i => (e i : ℂ)) - P) ^ 2 =
      (∑ i, (e i ^ 2 * (1 - (P i i).re) + (1 - e i) ^ 2 * (P i i).re)) / d := by
  have hD : IsSelfAdjoint (Matrix.diagonal (fun i => (e i : ℂ))) := by
    show star (Matrix.diagonal (fun i => (e i : ℂ))) = _
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  rw [hsNorm_sub_sq_selfAdjoint hD hP.isSelfAdjoint, hP.isIdempotentElem.eq,
    Matrix.diagonal_mul_diagonal, normalizedTrace_diagonal_mul_real]
  have hsq : (Matrix.diagonal (fun i => (e i : ℂ) * (e i : ℂ))) =
      Matrix.diagonal (fun i => ((e i ^ 2 : ℝ) : ℂ)) := by
    congr 1
    funext i
    rw [Complex.ofReal_pow]
    ring
  rw [hsq, normalizedTrace_diagonal_real, normalizedTrace_re]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  have hsum : (∑ i, (e i ^ 2 * (1 - (P i i).re) + (1 - e i) ^ 2 * (P i i).re)) =
      (∑ i, e i ^ 2) - 2 * (∑ i, e i * (P i i).re) + ∑ i, (P i i).re := by
    calc
      _ = ∑ i, (e i ^ 2 - 2 * (e i * (P i i).re) + (P i i).re) :=
        Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  ring

theorem matrixProjection_trace_difference_le (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    |(normalizedTrace P).re - (normalizedTrace Q).re| ≤ hsNorm (P - Q) ^ 2 := by
  have hpq := normalizedTrace_mul_nonneg P (1 - Q) hP.nonneg hQ.one_sub_nonneg
  have hqp := normalizedTrace_mul_nonneg (1 - P) Q hP.one_sub_nonneg hQ.nonneg
  have hpq' := (Complex.nonneg_iff.mp hpq).1
  have hqp' := (Complex.nonneg_iff.mp hqp).1
  simp only [mul_sub, sub_mul, mul_one, one_mul, normalizedTrace_sub, Complex.sub_re] at hpq' hqp'
  rw [hsNorm_sub_sq_selfAdjoint hP.isSelfAdjoint hQ.isSelfAdjoint,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, abs_le]
  constructor <;> linarith

end ThomGame.Analysis
