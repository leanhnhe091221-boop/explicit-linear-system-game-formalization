module

public import ThomGame.Analysis.MatrixResolventDifferentialBound
public import ThomGame.Analysis.MatrixResolventFamilies
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrated resolvent commutator bounds

The genuine differential inequality is integrated on every projection
step. The potential differences telescope from the scalar matrix,
leaving a dimension-free bound for the sum of the actual integrals.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MeasureTheory

variable {d : Nat}

noncomputable def matrixResolventColumnEnergy (lam : ℝ) (S F U : CMatrix d) (t : ℝ) : ℝ :=
  hsNorm ((U * matrixAffineResolvent lam S F t - matrixAffineResolvent lam S F t * U) * F) ^ 2

theorem matrixResolventColumnEnergy_nonneg (lam : ℝ) (S F U : CMatrix d) (t : ℝ) :
    0 ≤ matrixResolventColumnEnergy lam S F U t := sq_nonneg _

theorem matrixResolventColumnEnergy_continuousOn [NeZero d] {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) (U : CMatrix d) :
    ContinuousOn (matrixResolventColumnEnergy lam S F U) (Set.Ici 0) := by
  have hD := matrixAffineResolvent_continuousOn hlam hS hF
  exact (continuous_hsNorm.comp_continuousOn
    (((continuousOn_const.mul hD).sub (hD.mul continuousOn_const)).mul continuousOn_const)).pow 2

theorem matrixResolvent_integrated_step [NeZero d] {lam : ℝ} {S F U : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    (lam / 2) * (∫ t in (0 : ℝ)..1, matrixResolventColumnEnergy lam S F U t) ≤
      (2 / lam) * hsNorm (U * F - F * U) ^ 2 +
        matrixResolventPotential (lam • 1 + S) U - matrixResolventPotential (lam • 1 + (S + F)) U := by
  let G : ℝ → ℝ := fun t => matrixResolventPotential (lam • 1 + S + t • F) U
  let Z := matrixResolventColumnEnergy lam S F U
  have hZ : ContinuousOn Z (Set.Icc 0 1) :=
    (matrixResolventColumnEnergy_continuousOn hlam hS hF.nonneg U).mono fun _ ht => ht.1
  have hG : ContinuousOn G (Set.Icc 0 1) := fun t ht =>
    (matrixResolventPotential_hasDerivAt hlam hS hF.nonneg ht.1 U).continuousAt.continuousWithinAt
  have hdiff (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : HasDerivWithinAt G (deriv G t) (Set.Ioi t) t :=
    (matrixResolventPotential_hasDerivAt hlam hS hF.nonneg ht.1.le U).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hphi : ContinuousOn (fun t => (2 / lam) * hsNorm (U * F - F * U) ^ 2 - (lam / 2) * Z t)
      (Set.Icc 0 1) := continuousOn_const.sub (continuousOn_const.mul hZ)
  have he := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hG hdiff hphi.integrableOn_Icc (fun t ht =>
      matrixResolventPotential_derivative_bound hlam hS hF ht.1.le hU hUU)
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((hZ.intervalIntegrable_of_Icc (by norm_num)).const_mul (lam / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at he
  simp only [G, zero_smul, one_smul, add_zero, sub_zero, one_smul, smul_eq_mul, one_mul] at he
  simp only [intervalIntegral.integral_const_mul] at he
  rw [add_assoc] at he
  linarith

theorem matrixResolvent_integrated_partial_sum [NeZero d] {lam : ℝ}
    (hlam : 0 < lam) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (U : CMatrix d) (hU : IsSelfAdjoint U) (hUU : U * U = 1) (n : Nat) :
    (lam / 2) * (∑ i ∈ Finset.range n, ∫ t in (0 : ℝ)..1,
      matrixResolventColumnEnergy lam (matrixProjectionPartialSum 0 F i) (F i) U t) ≤
      (2 / lam) * (∑ i ∈ Finset.range n, hsNorm (U * F i - F i * U) ^ 2) -
        matrixResolventPotential (lam • 1 + matrixProjectionPartialSum 0 F n) U := by
  induction n with
  | zero => simp [matrixResolventPotential_scalar hlam hU hUU]
  | succ n ih =>
    have he := matrixResolvent_integrated_step hlam
      (matrixProjectionPartialSum_nonneg (le_refl 0) F hF n) (hF n) hU hUU
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add,
      matrixProjectionPartialSum_succ]
    linarith

theorem matrixResolvent_integrated_family [NeZero d] {lam : ℝ}
    (hlam : 0 < lam) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (U : CMatrix d) (hU : IsSelfAdjoint U) (hUU : U * U = 1) (n : Nat) :
    (∑ i ∈ Finset.range n, ∫ t in (0 : ℝ)..1,
      matrixResolventColumnEnergy lam (matrixProjectionPartialSum 0 F i) (F i) U t) ≤
      (4 / lam ^ 2) * (∑ i ∈ Finset.range n, hsNorm (U * F i - F i * U) ^ 2) := by
  have he := matrixResolvent_integrated_partial_sum hlam F hF U hU hUU n
  have hp := matrixResolventPotential_nonneg hlam
    (matrixProjectionPartialSum_nonneg (le_refl 0) F hF n) hU hUU
  have hbound : (lam / 2) * (∑ i ∈ Finset.range n, ∫ t in (0 : ℝ)..1,
      matrixResolventColumnEnergy lam (matrixProjectionPartialSum 0 F i) (F i) U t) ≤
      (2 / lam) * (∑ i ∈ Finset.range n, hsNorm (U * F i - F i * U) ^ 2) := by linarith
  have hcoef : (lam / 2) * (4 / lam ^ 2) = 2 / lam := by field_simp; norm_num
  apply (mul_le_mul_iff_right₀ (show 0 < lam / 2 by positivity)).mp
  rw [← mul_assoc, hcoef]
  exact hbound

end ThomGame.Analysis
