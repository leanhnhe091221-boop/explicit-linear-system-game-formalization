module

public import ThomGame.Analysis.MatrixResolventEndpoint

/-!
# The summed resolvent estimate for self-adjoint unitaries

Integrating the initial-point comparison over [0,lambda/2] and then
using the telescoped potential proves ALT (3.2) in the self-adjoint
unitary case, with the explicit absolute constant 146.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MeasureTheory

variable {d : Nat} [NeZero d]

theorem matrixResolvent_endpoint_integral_bound {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hS : 0 ≤ S) (hF : IsStarProjection F) (U : CMatrix d) :
    (lam / 2) * hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F) ^ 2 ≤
      18 * (∫ t in (0 : ℝ)..1, matrixResolventColumnEnergy lam S F U t) +
        lam⁻¹ * hsNorm (U * F - F * U) ^ 2 := by
  let x := hsNorm ((U * matrixPositiveResolvent lam S - matrixPositiveResolvent lam S * U) * F)
  let e := hsNorm (U * F - F * U)
  let Z := matrixResolventColumnEnergy lam S F U
  have hhalf0 : (0 : ℝ) ≤ lam / 2 := by positivity
  have hhalf1 : lam / 2 ≤ 1 := by linarith
  have hZ := matrixResolventColumnEnergy_continuousOn hlam hS hF.nonneg U
  have hi : IntervalIntegrable Z volume 0 1 :=
    (hZ.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc (by norm_num)
  have his : IntervalIntegrable Z volume 0 (lam / 2) :=
    (hZ.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hhalf0
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 (lam / 2)) : x ^ 2 ≤ 18 * Z t + 2 * (lam⁻¹ * e) ^ 2 := by
    have he := matrixResolvent_column_endpoint_bound hlam hS hF ht.1 ht.2 U
    let y := hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F)
    change x ≤ 3 * y + lam⁻¹ * e at he
    change x ^ 2 ≤ 18 * y ^ 2 + 2 * (lam⁻¹ * e) ^ 2
    have hx : 0 ≤ x := hsNorm_nonneg _
    have hy : 0 ≤ y := hsNorm_nonneg _
    have he0 : 0 ≤ lam⁻¹ * e := mul_nonneg (inv_nonneg.mpr hlam.le) (hsNorm_nonneg _)
    nlinarith [sq_nonneg (3 * y - lam⁻¹ * e)]
  have he := intervalIntegral.integral_mono_on hhalf0 intervalIntegrable_const
    ((his.const_mul 18).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (his.const_mul 18) intervalIntegrable_const] at he
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    sub_zero, smul_eq_mul] at he
  have hm : (∫ t in (0 : ℝ)..(lam / 2), Z t) ≤ ∫ t in (0 : ℝ)..1, Z t :=
    intervalIntegral.integral_mono_interval le_rfl hhalf0 hhalf1
      (Filter.Eventually.of_forall (matrixResolventColumnEnergy_nonneg lam S F U)) hi
  have hc : 2 * ((lam / 2) * (lam⁻¹ * e) ^ 2) = lam⁻¹ * e ^ 2 := by field_simp
  rw [hc] at he
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) le_rfl)

omit [NeZero d] in
theorem resolvent_endpoint_total_bound {lam E X Z : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hE : 0 ≤ E) (hZ : Z ≤ (4 / lam ^ 2) * E)
    (hX : (lam / 2) * X ≤ 18 * Z + lam⁻¹ * E) : X ≤ (146 / lam ^ 3) * E := by
  have hcoef : 72 / lam ^ 2 + lam⁻¹ ≤ 73 / lam ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hlam)).mp
    have hleft : lam ^ 2 * (72 / lam ^ 2 + lam⁻¹) = 72 + lam := by field_simp
    have hright : lam ^ 2 * (73 / lam ^ 2) = 73 := by field_simp
    rw [hleft, hright]
    linarith
  have he : (lam / 2) * X ≤ (73 / lam ^ 2) * E := by
    calc
      _ ≤ 18 * Z + lam⁻¹ * E := hX
      _ ≤ 18 * ((4 / lam ^ 2) * E) + lam⁻¹ * E := by gcongr
      _ = (72 / lam ^ 2 + lam⁻¹) * E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE
  have hc : (lam / 2) * (146 / lam ^ 3) = 73 / lam ^ 2 := by field_simp; norm_num
  apply (mul_le_mul_iff_right₀ (show 0 < lam / 2 by positivity)).mp
  rw [← mul_assoc, hc]
  exact he

theorem matrixResolvent_selfAdjoint_family_bound {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (U : CMatrix d) (hU : IsSelfAdjoint U) (hUU : U * U = 1) (n : Nat) :
    (∑ i ∈ Finset.range n, hsNorm ((U * matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i) -
      matrixPositiveResolvent lam (matrixProjectionPartialSum 0 F i) * U) * F i) ^ 2) ≤
      (146 / lam ^ 3) * (∑ i ∈ Finset.range n, hsNorm (U * F i - F i * U) ^ 2) := by
  have hi := matrixResolvent_integrated_family hlam F hF U hU hUU n
  have he := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    matrixResolvent_endpoint_integral_bound hlam hlam1
      (matrixProjectionPartialSum_nonneg (le_refl 0) F hF i) (hF i) U)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at he
  exact resolvent_endpoint_total_bound hlam hlam1
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hi he

end ThomGame.Analysis
