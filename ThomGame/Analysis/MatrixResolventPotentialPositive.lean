module

public import ThomGame.Analysis.MatrixResolventPotential

/-!
# Positivity of the actual resolvent potential

For a self-adjoint involution the potential is exactly half the
squared Hilbert--Schmidt norm of the commutator conjugated by the
positive square root of the actual inverse.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem normalizedTrace_sandwich_gram (B X : CMatrix d) (hB : IsSelfAdjoint B) :
    normalizedTrace (star (B * X * B) * (B * X * B)) =
      normalizedTrace (star X * (B * B) * X * (B * B)) := by
  simp only [star_mul, hB.star_eq]
  calc
    _ = normalizedTrace (B * (star X * (B * B) * X * B)) := by congr 1; noncomm_ring
    _ = normalizedTrace ((star X * (B * B) * X * B) * B) := normalizedTrace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

theorem normalizedTrace_inverse_commutator_gram [NeZero d] {A R U : CMatrix d}
    (hA : IsSelfAdjoint A) (hU : IsSelfAdjoint U)
    (hUU : U * U = 1) (hAR : A * R = 1) (hRA : R * A = 1) :
    normalizedTrace (star (U * A - A * U) * R * (U * A - A * U) * R) =
      2 * normalizedTrace (A * U * R * U) - 2 := by
  have he : star (U * A - A * U) * R * (U * A - A * U) * R =
      A * U * R * U + U * A * U * R - (1 + 1) := by
    simp only [star_sub, star_mul, hA.star_eq, hU.star_eq]
    calc
      _ = A * U * R * U * (A * R) - A * U * (R * A) * U * R -
          U * (A * R) * U * (A * R) + U * (A * R) * A * U * R := by noncomm_ring
      _ = _ := by
        simp only [hAR, hRA, mul_one]
        rw [mul_assoc A U U, hUU, mul_one, hAR]
        abel
  rw [he, normalizedTrace_sub, normalizedTrace_add, normalizedTrace_add, normalizedTrace_one]
  have hc : normalizedTrace (U * A * U * R) = normalizedTrace (A * U * R * U) := by
    rw [mul_assoc U A U, mul_assoc U (A * U) R, normalizedTrace_mul_comm U]
  rw [hc]
  ring

theorem matrixResolventPotential_eq_hsNorm_sq [NeZero d] {lam : ℝ} {S U : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    matrixResolventPotential (lam • 1 + S) U = (1 / 2 : ℝ) *
      hsNorm (CFC.sqrt (matrixPositiveResolvent lam S) *
        (U * (lam • 1 + S) - (lam • 1 + S) * U) *
          CFC.sqrt (matrixPositiveResolvent lam S)) ^ 2 := by
  have hR := matrixPositiveResolvent_nonneg hlam hS
  have hA : IsSelfAdjoint (lam • (1 : CMatrix d) + S) :=
    (add_nonneg (smul_nonneg hlam.le zero_le_one) hS).isSelfAdjoint
  have he := normalizedTrace_sandwich_gram (CFC.sqrt (matrixPositiveResolvent lam S))
    (U * (lam • 1 + S) - (lam • 1 + S) * U) (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [CFC.sqrt_mul_sqrt_self _ hR,
    normalizedTrace_inverse_commutator_gram hA hU hUU
      (matrixPositiveResolvent_shift_mul hlam hS) (matrixPositiveResolvent_mul_shift hlam hS),
    normalizedTrace_gram] at he
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.mul_re] at hr
  norm_num at hr
  rw [matrixResolventPotential, ← matrixPositiveResolvent_eq_inverse hlam hS]
  linarith

theorem matrixResolventPotential_nonneg [NeZero d] {lam : ℝ} {S U : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    0 ≤ matrixResolventPotential (lam • 1 + S) U := by
  rw [matrixResolventPotential_eq_hsNorm_sq hlam hS hU hUU]
  positivity

theorem matrixResolventPotential_scalar [NeZero d] {lam : ℝ} {U : CMatrix d}
    (hlam : 0 < lam) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    matrixResolventPotential (lam • 1) U = 0 := by
  have he := matrixResolventPotential_eq_hsNorm_sq hlam (le_refl (0 : CMatrix d)) hU hUU
  simpa only [add_zero, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self,
    mul_zero, zero_mul, hsNorm_zero, zero_pow (by decide : 2 ≠ 0)] using he

end ThomGame.Analysis
