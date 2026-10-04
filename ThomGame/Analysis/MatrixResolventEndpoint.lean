module

public import ThomGame.Analysis.MatrixResolventIntegratedBound

/-!
# Comparing the initial resolvent to an interior point

The actual inverse identity and the product rule for commutators give
z(0) <= 3 z(t) + lambda^-1 epsilon for 0 <= t <= lambda/2.
No self-adjointness assumption on the matrix U is needed here.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem hsNorm_real_smul (t : ℝ) (X : CMatrix d) : hsNorm (t • X) = |t| * hsNorm X := by
  have he : t • X = (t : ℂ) • X := by ext i j; simp [Complex.real_smul]
  rw [he, hsNorm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem hsNorm_mul_projection_le (X : CMatrix d) {F : CMatrix d} (hF : IsStarProjection F) :
    hsNorm (X * F) ≤ hsNorm X := by
  exact (hsNorm_mul_le_right X F).trans
    (by simpa only [matrixOpNorm, mul_one] using!
      mul_le_mul_of_nonneg_left (hF.norm_le F) (hsNorm_nonneg X))

theorem hsNorm_projection_mul_le {F : CMatrix d} (hF : IsStarProjection F) (X : CMatrix d) :
    hsNorm (F * X) ≤ hsNorm X := by
  exact (hsNorm_mul_le_left F X).trans
    (by simpa only [matrixOpNorm, one_mul] using!
      mul_le_mul_of_nonneg_right (hF.norm_le F) (hsNorm_nonneg X))

theorem matrixAffineResolvent_initial_identity {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) (ht : 0 ≤ t) :
    matrixPositiveResolvent lam S = matrixAffineResolvent lam S F t +
      t • (matrixPositiveResolvent lam S * F * matrixAffineResolvent lam S F t) := by
  have he := matrixPositiveResolvent_difference hlam hS (add_nonneg hS (smul_nonneg ht hF))
  rw [add_sub_cancel_left, mul_smul_comm, smul_mul_assoc,
    ← matrixAffineResolvent_eq_positive hlam hS hF ht] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem matrix_inverse_update_commutator_column {R T F U : CMatrix d} {t : ℝ}
    (hR : R = T + t • (R * F * T)) :
    (U * R - R * U) * F = (U * T - T * U) * F + t •
      (((U * R - R * U) * F) * T * F + R * (U * F - F * U) * T * F +
        R * F * ((U * T - T * U) * F)) := by
  have hp : (U * (R * F * T) - (R * F * T) * U) * F =
      (((U * R - R * U) * F) * T * F + R * (U * F - F * U) * T * F +
        R * F * ((U * T - T * U) * F)) := by noncomm_ring
  calc
    _ = (U * (T + t • (R * F * T)) - (T + t • (R * F * T)) * U) * F :=
      congrArg (fun X => (U * X - X * U) * F) hR
    _ = (U * T - T * U) * F + t • ((U * (R * F * T) - (R * F * T) * U) * F) := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, sub_mul, smul_sub]
      abel
    _ = _ := by rw [hp]

set_option maxHeartbeats 800000 in
theorem matrixResolvent_column_comparison {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) (ht : 0 ≤ t) (U : CMatrix d) :
    hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) ≤
      hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F) +
        t * (lam⁻¹ * hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) +
          lam⁻¹ ^ 2 * hsNorm (U * F - F * U) +
          lam⁻¹ * hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F)) := by
  let R := matrixPositiveResolvent lam S
  let T := matrixAffineResolvent lam S F t
  let C := (U * R - R * U) * F
  let K := (U * T - T * U) * F
  let E := U * F - F * U
  have hR : matrixOpNorm R ≤ lam⁻¹ := matrixPositiveResolvent_norm_le hlam hS
  have hT : matrixOpNorm T ≤ lam⁻¹ := by
    dsimp [T]
    rw [matrixAffineResolvent_eq_positive hlam hS hF.nonneg ht]
    exact matrixPositiveResolvent_norm_le hlam (add_nonneg hS (smul_nonneg ht hF.nonneg))
  have hfirst : hsNorm (C * T * F) ≤ lam⁻¹ * hsNorm C := by
    apply (hsNorm_mul_projection_le _ hF).trans
    exact (hsNorm_mul_le_right C T).trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hT (hsNorm_nonneg C))
  have hsecond : hsNorm (R * E * T * F) ≤ lam⁻¹ ^ 2 * hsNorm E := by
    apply (hsNorm_mul_projection_le _ hF).trans
    calc
      _ ≤ matrixOpNorm R * hsNorm E * matrixOpNorm T :=
        (hsNorm_mul_le_right _ _).trans
          (mul_le_mul_of_nonneg_right (hsNorm_mul_le_left _ _) (matrixOpNorm_nonneg _))
      _ ≤ lam⁻¹ * hsNorm E * lam⁻¹ := mul_le_mul
        (mul_le_mul_of_nonneg_right hR (hsNorm_nonneg _)) hT
        (matrixOpNorm_nonneg _) (mul_nonneg (inv_nonneg.mpr hlam.le) (hsNorm_nonneg _))
      _ = _ := by ring
  have hthird : hsNorm (R * F * K) ≤ lam⁻¹ * hsNorm K := by
    rw [mul_assoc]
    calc
      _ ≤ matrixOpNorm R * hsNorm (F * K) := hsNorm_mul_le_left _ _
      _ ≤ lam⁻¹ * hsNorm K := mul_le_mul hR (hsNorm_projection_mul_le hF K)
        (hsNorm_nonneg _) (inv_nonneg.mpr hlam.le)
  have hid := matrix_inverse_update_commutator_column
    (matrixAffineResolvent_initial_identity hlam hS hF.nonneg ht) (U := U)
  change C = K + t • (C * T * F + R * E * T * F + R * F * K) at hid
  change hsNorm C ≤ hsNorm K + t * (lam⁻¹ * hsNorm C + lam⁻¹ ^ 2 * hsNorm E + lam⁻¹ * hsNorm K)
  have hs := (hsNorm_add_le (C * T * F + R * E * T * F) (R * F * K)).trans
    (add_le_add (hsNorm_add_le (C * T * F) (R * E * T * F)) le_rfl)
  calc
    _ ≤ hsNorm K + |t| * hsNorm (C * T * F + R * E * T * F + R * F * K) := by
      nth_rw 1 [hid]
      simpa only [hsNorm_real_smul] using hsNorm_add_le K (t • (C * T * F + R * E * T * F + R * F * K))
    _ ≤ _ := by
      rw [abs_of_nonneg ht]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (hs.trans (add_le_add (add_le_add hfirst hsecond) hthird)) ht)

theorem matrixResolvent_column_endpoint_bound {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F)
    (ht : 0 ≤ t) (htlam : t ≤ lam / 2) (U : CMatrix d) :
    hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) ≤
      3 * hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F) +
        lam⁻¹ * hsNorm (U * F - F * U) := by
  have he := matrixResolvent_column_comparison hlam hS hF ht U
  have hhalf := mul_le_mul_of_nonneg_right htlam (inv_nonneg.mpr hlam.le)
  have hmul : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
  let x := hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F)
  let y := hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F)
  let e := hsNorm (U * F - F * U)
  change x ≤ y + t * (lam⁻¹ * x + lam⁻¹ ^ 2 * e + lam⁻¹ * y) at he
  change x ≤ 3 * y + lam⁻¹ * e
  have hx : 0 ≤ x := hsNorm_nonneg _
  have hy : 0 ≤ y := hsNorm_nonneg _
  have he0 : 0 ≤ e := hsNorm_nonneg _
  have hsmall : t * lam⁻¹ ≤ 1 / 2 := by nlinarith [hmul]
  have h1 := mul_le_mul_of_nonneg_right hsmall hx
  have h2 := mul_le_mul_of_nonneg_right hsmall hy
  have h3 := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (inv_nonneg.mpr hlam.le) he0)
  nlinarith

end ThomGame.Analysis
