module

public import ThomGame.Analysis.MatrixResolventCoreCommutator

/-!
# Boundary energy of the actual resolvent factors

The inverse-square-root estimate controls the three product-rule terms
in X=sqrt(lambda) R F sqrt((I+FRF)^-1). Squaring gives the local bound
needed before summing Lemma 3.2.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem resolvent_factor_coeff_bound {lam e z : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (he : 0 ≤ e) (hz : 0 ≤ z) :
    z + lam⁻¹ * e + lam⁻¹ * (lam⁻¹ * e + (1 / 2 : ℝ) * z) ≤
      2 * lam⁻¹ ^ 2 * e + 2 * lam⁻¹ * z := by
  have hi : 1 ≤ lam⁻¹ := by simpa using one_div_le_one_div_of_le hlam hlam1
  have h1 := mul_le_mul_of_nonneg_right hi hz
  have h2 := mul_le_mul_of_nonneg_right hi (mul_nonneg (inv_nonneg.mpr hlam.le) he)
  nlinarith

theorem resolvent_factor_square_bound {lam x e z : ℝ} (hlam : 0 < lam) (hx0 : 0 ≤ x)
    (hx : x ≤ Real.sqrt lam * (2 * lam⁻¹ ^ 2 * e + 2 * lam⁻¹ * z)) :
    x ^ 2 ≤ (8 / lam ^ 3) * e ^ 2 + (8 / lam) * z ^ 2 := by
  have hs := mul_self_le_mul_self hx0 hx
  rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt hlam.le] at hs
  have hsq := mul_nonneg hlam.le (sq_nonneg (lam⁻¹ ^ 2 * e - lam⁻¹ * z))
  have hb : x ^ 2 ≤ 8 * lam * (lam⁻¹ ^ 4 * e ^ 2 + lam⁻¹ ^ 2 * z ^ 2) := by nlinarith
  have heq : 8 * lam * (lam⁻¹ ^ 4 * e ^ 2 + lam⁻¹ ^ 2 * z ^ 2) =
      (8 / lam ^ 3) * e ^ 2 + (8 / lam) * z ^ 2 := by field_simp
  exact hb.trans_eq heq

variable {d : Nat}

theorem hsNorm_projection_resolvent_factor_commutator_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : CMatrix d) :
    hsNorm (U * matrixProjectionResolventFactor lam S F - matrixProjectionResolventFactor lam S F * U) ≤
      Real.sqrt lam * (2 * lam⁻¹ ^ 2 * hsNorm (U * F - F * U) + 2 * lam⁻¹ *
        hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F)) := by
  let R := matrixPositiveResolvent lam S
  let B := CFC.sqrt (matrixPositiveResolvent 1 (matrixProjectionResolventCore lam S F))
  let E := U * F - F * U
  let K := (U * R - R * U) * F
  let C := U * B - B * U
  have hR : matrixOpNorm R ≤ lam⁻¹ := matrixPositiveResolvent_norm_le hlam hS
  have hB : matrixOpNorm B ≤ 1 := matrixResolventSqrt_norm_le (matrixProjectionResolventCore_nonneg hlam hS hF)
  have hC : hsNorm C ≤ lam⁻¹ * hsNorm E + (1 / 2 : ℝ) * hsNorm K :=
    hsNorm_projection_resolvent_sqrt_commutator_le hlam hS hF U
  have h1 : hsNorm (K * B) ≤ hsNorm K :=
    (hsNorm_mul_le_right _ _).trans (by simpa using mul_le_mul_of_nonneg_left hB (hsNorm_nonneg K))
  have h2 : hsNorm (R * E * B) ≤ lam⁻¹ * hsNorm E := by
    calc
      _ ≤ hsNorm (R * E) := (hsNorm_mul_le_right _ _).trans
        (by simpa using mul_le_mul_of_nonneg_left hB (hsNorm_nonneg (R * E)))
      _ ≤ matrixOpNorm R * hsNorm E := hsNorm_mul_le_left _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (hsNorm_nonneg E)
  have h3 : hsNorm (R * F * C) ≤ lam⁻¹ * hsNorm C := by
    rw [mul_assoc]
    exact (hsNorm_mul_le_left _ _).trans (mul_le_mul hR (hsNorm_projection_mul_le hF C)
      (hsNorm_nonneg _) (inv_nonneg.mpr hlam.le))
  have hid : U * (R * F * B) - (R * F * B) * U = K * B + R * E * B + R * F * C := by
    dsimp [K, E, C]; noncomm_ring
  change hsNorm (U * (Real.sqrt lam • (R * F * B)) - (Real.sqrt lam • (R * F * B)) * U) ≤
    Real.sqrt lam * (2 * lam⁻¹ ^ 2 * hsNorm E + 2 * lam⁻¹ * hsNorm K)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hsNorm_real_smul,
    abs_of_nonneg (Real.sqrt_nonneg _), hid]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ hsNorm (K * B) + hsNorm (R * E * B) + hsNorm (R * F * C) :=
      (hsNorm_add_le _ _).trans (add_le_add (hsNorm_add_le _ _) le_rfl)
    _ ≤ hsNorm K + lam⁻¹ * hsNorm E + lam⁻¹ * hsNorm C := add_le_add (add_le_add h1 h2) h3
    _ ≤ hsNorm K + lam⁻¹ * hsNorm E + lam⁻¹ * (lam⁻¹ * hsNorm E + (1 / 2 : ℝ) * hsNorm K) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hlam.le))
    _ ≤ _ := resolvent_factor_coeff_bound hlam hlam1 (hsNorm_nonneg E) (hsNorm_nonneg K)

theorem hsNorm_projection_resolvent_factor_commutator_sq_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : CMatrix d) :
    hsNorm (U * matrixProjectionResolventFactor lam S F - matrixProjectionResolventFactor lam S F * U) ^ 2 ≤
      (8 / lam ^ 3) * hsNorm (U * F - F * U) ^ 2 + (8 / lam) *
        hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) ^ 2 :=
  resolvent_factor_square_bound hlam (hsNorm_nonneg _)
    (hsNorm_projection_resolvent_factor_commutator_le hlam hlam1 hS hF U)

theorem hsNorm_projection_resolvent_difference_commutator_sq_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : UnitaryMatrix d) :
    hsNorm (U.val * matrixProjectionResolventDifference lam S F - matrixProjectionResolventDifference lam S F * U.val) ^ 2 ≤
      (32 / lam ^ 3) * hsNorm (U.val * F - F * U.val) ^ 2 + (32 / lam) *
        hsNorm ((U.val * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U.val) * F) ^ 2 := by
  have he := hsNorm_unitary_commutator_gram_le U (matrixProjectionResolventFactor lam S F)
    (matrixProjectionResolventFactor_norm_le hlam hS hF)
  rw [← matrixProjectionResolventDifference_eq_factor hlam hS hF] at he
  have hs := mul_self_le_mul_self (hsNorm_nonneg _) he
  have hf := hsNorm_projection_resolvent_factor_commutator_sq_le hlam hlam1 hS hF U.val
  have hs' : hsNorm (U.val * matrixProjectionResolventDifference lam S F -
      matrixProjectionResolventDifference lam S F * U.val) ^ 2 ≤
        4 * hsNorm (U.val * matrixProjectionResolventFactor lam S F -
          matrixProjectionResolventFactor lam S F * U.val) ^ 2 := by nlinarith [hs]
  exact hs'.trans ((mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

end ThomGame.Analysis
