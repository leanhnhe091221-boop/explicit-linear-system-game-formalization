module

public import ThomGame.Analysis.MatrixCommutatorProducts

/-!
# Commutators of the compressed resolvent core

The three product-rule terms are estimated with the column-restricted
resolvent commutator. Functional calculus then controls the actual
inverse square root appearing in the factor X_i of ALT Lemma 3.3.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem hsNorm_projection_resolvent_core_commutator_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : CMatrix d) :
    hsNorm (U * matrixProjectionResolventCore lam S F - matrixProjectionResolventCore lam S F * U) ≤
      2 * lam⁻¹ * hsNorm (U * F - F * U) +
        hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) := by
  let R := matrixPositiveResolvent lam S
  let E := U * F - F * U
  let K := (U * R - R * U) * F
  have hR : matrixOpNorm R ≤ lam⁻¹ := matrixPositiveResolvent_norm_le hlam hS
  have he : U * (F * R * F) - (F * R * F) * U = E * R * F + F * K + F * R * E := by
    dsimp [E, K]; noncomm_ring
  have h1 : hsNorm (E * R * F) ≤ lam⁻¹ * hsNorm E :=
    (hsNorm_mul_projection_le _ hF).trans ((hsNorm_mul_le_right _ _).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hR (hsNorm_nonneg E)))
  have h2 : hsNorm (F * K) ≤ hsNorm K := hsNorm_projection_mul_le hF K
  have h3 : hsNorm (F * R * E) ≤ lam⁻¹ * hsNorm E := by
    rw [mul_assoc]
    exact (hsNorm_projection_mul_le hF _).trans ((hsNorm_mul_le_left _ _).trans
      (mul_le_mul_of_nonneg_right hR (hsNorm_nonneg E)))
  change hsNorm (U * (F * R * F) - (F * R * F) * U) ≤ 2 * lam⁻¹ * hsNorm E + hsNorm K
  rw [he]
  have ht := (hsNorm_add_le (E * R * F + F * K) (F * R * E)).trans
    (add_le_add (hsNorm_add_le (E * R * F) (F * K)) le_rfl)
  linarith

theorem hsNorm_projection_resolvent_sqrt_commutator_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : CMatrix d) :
    hsNorm (U * CFC.sqrt (matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F)) -
      CFC.sqrt (matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F)) * U) ≤
        lam⁻¹ * hsNorm (U * F - F * U) + (1 / 2 : ℝ) *
          hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) := by
  have he := hsNorm_resolventSqrt_commutator_le (matrixProjectionResolventCore_nonneg hlam hS hF) U
  have hc := hsNorm_projection_resolvent_core_commutator_le hlam hS hF U
  linarith

end ThomGame.Analysis
