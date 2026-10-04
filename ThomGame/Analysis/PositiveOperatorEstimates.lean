module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Positive operator estimates and weak closedness of order

The quadratic form of a positive operator controls the squared norm of
its action. The actual Loewner positive cone is weak operator closed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operator_re_inner_mono {A B : H →L[ℂ] H} (hAB : A ≤ B) (x : H) :
    (inner ℂ x (A x)).re ≤ (inner ℂ x (B x)).re := by
  have h := (ContinuousLinearMap.le_def.mp hAB).re_inner_nonneg_right x
  simpa only [sub_apply, inner_sub_right, map_sub, RCLike.re_to_complex, sub_nonneg] using h

variable [CompleteSpace H]

theorem positive_operator_sq_le (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖A‖ ≤ K) : A * A ≤ K • A := by
  have hle : A ≤ algebraMap ℝ (H →L[ℂ] H) K :=
    (CStarAlgebra.norm_le_iff_le_algebraMap A hK hA).mp hbound
  have hc : Commute A (algebraMap ℝ (H →L[ℂ] H) K - A) :=
    (Algebra.commute_algebraMap_right K A).sub_right (Commute.refl A)
  have hp := Commute.mul_nonneg hA (sub_nonneg.mpr hle) hc
  rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at hp
  exact sub_nonneg.mp hp

theorem positive_operator_apply_norm_sq_le (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖A‖ ≤ K) (x : H) :
    ‖A x‖ ^ 2 ≤ K * (inner ℂ x (A x)).re := by
  have h := operator_re_inner_mono (positive_operator_sq_le A hA K hK hbound) x
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_left_eq_inner_right x (A x)
  rw [mul_apply_eq_comp, ← hs, smul_apply, ← Complex.coe_smul, inner_smul_right] at h
  have hh : (inner ℂ (A x) (A x)).re = ‖A x‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (A x)
  simpa only [hh, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

theorem wot_nonneg_iff (T : H →WOT[ℂ] H) :
    0 ≤ T.toCLM ↔ star T = T ∧ ∀ x : H, 0 ≤ (inner ℂ x (T x)).re := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨congrArg ContinuousLinearMapWOT.ofCLM hs.star_eq, ?_⟩
    intro x
    simpa only [ContinuousLinearMap.reApplyInnerSelf, inner_re_symm, RCLike.re_to_complex,
      ContinuousLinearMapWOT.coe_toCLM] using hp x
  · rintro ⟨hs, hp⟩
    refine ⟨congrArg ContinuousLinearMapWOT.toCLM hs, ?_⟩
    intro x
    simpa only [ContinuousLinearMap.reApplyInnerSelf, inner_re_symm, RCLike.re_to_complex,
      ContinuousLinearMapWOT.coe_toCLM] using hp x

theorem wot_nonneg_isClosed : IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := by
  simp_rw [wot_nonneg_iff]
  change IsClosed ({T : H →WOT[ℂ] H | star T = T} ∩ {T | ∀ x : H, 0 ≤ (inner ℂ x (T x)).re})
  refine (isClosed_eq continuous_star continuous_id).inter ?_
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun x => ?_
  exact isClosed_le continuous_const (Complex.continuous_re.comp
    (ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ x)))

theorem wot_le_isClosed (A : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | A ≤ T.toCLM} := by
  convert (wot_nonneg_isClosed (H := H)).preimage
    (continuous_id.sub (continuous_const (y := ContinuousLinearMapWOT.ofCLM A))) using 1
  ext T
  change A ≤ T.toCLM ↔ 0 ≤ T.toCLM - A
  exact sub_nonneg.symm

theorem wot_ge_isClosed (A : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ≤ A} := by
  convert (wot_nonneg_isClosed (H := H)).preimage
    ((continuous_const (y := ContinuousLinearMapWOT.ofCLM A)).sub continuous_id) using 1
  ext T
  change T.toCLM ≤ A ↔ 0 ≤ A - T.toCLM
  exact sub_nonneg.symm

end ThomGame.Analysis
