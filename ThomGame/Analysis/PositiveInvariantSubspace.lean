module

public import ThomGame.Analysis.PositiveOperatorEstimates
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Sharp power bounds on invariant Hilbert subspaces

A quadratic-form upper bound for a positive operator gives the same
operator-norm bound after restriction to an invariant complete subspace.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem positive_operator_restrict_nonneg (T : H →L[ℂ] H) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, T x ∈ S) (hT : 0 ≤ T) : 0 ≤ T.restrict hS := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
  exact ⟨fun x y => hp.isSymmetric x.val y.val, fun x => hp.2 x.val⟩

theorem continuousLinearMap_restrict_pow_apply (T : H →L[ℂ] H) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, T x ∈ S) (n : Nat) (x : S) :
    (((T.restrict hS) ^ n) x).val = (T ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      change T ((((T.restrict hS) ^ n) x).val) = _
      rw [ih]

variable [CompleteSpace H]

theorem positive_operator_norm_le_of_quadratic (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hform : ∀ x, (inner ℂ x (T x)).re ≤ K * ‖x‖ ^ 2) : ‖T‖ ≤ K := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap T hK hT).mpr
  apply ContinuousLinearMap.le_def.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((by rfl : IsSelfAdjoint K).algebraMap (H →L[ℂ] H)).sub
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint, ?_⟩
  intro x
  have hh : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) x
  change 0 ≤ (inner ℂ ((algebraMap ℝ (H →L[ℂ] H) K - T) x) x).re
  rw [← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex]
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hh, sub_nonneg] using hform x

omit [CompleteSpace H] in
theorem positive_operator_invariant_pow_norm_le (T : H →L[ℂ] H) (S : Submodule ℂ H)
    [CompleteSpace S] (hS : ∀ x ∈ S, T x ∈ S) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hform : ∀ x ∈ S, (inner ℂ x (T x)).re ≤ K * ‖x‖ ^ 2) (n : Nat) (x : H) (hx : x ∈ S) :
    ‖(T ^ n) x‖ ≤ K ^ n * ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, one_apply_eq_self, one_mul, le_refl]
  have hb : ‖T.restrict hS‖ ≤ K := positive_operator_norm_le_of_quadratic _
    (positive_operator_restrict_nonneg T S hS hT) K hK (fun x => hform x.val x.property)
  have hp' : ‖T.restrict hS‖ ^ n ≤ K ^ n :=
    pow_le_pow_left₀ (norm_nonneg (T.restrict hS)) hb n
  have hp : ‖(T.restrict hS) ^ n‖ ≤ K ^ n := (norm_pow_le' (T.restrict hS) hn).trans hp'
  have he := (((T.restrict hS) ^ n).le_opNorm (⟨x, hx⟩ : S)).trans
    (mul_le_mul_of_nonneg_right hp (norm_nonneg (⟨x, hx⟩ : S)))
  change ‖(((T.restrict hS) ^ n) (⟨x, hx⟩ : S)).val‖ ≤ K ^ n * ‖x‖ at he
  rwa [continuousLinearMap_restrict_pow_apply] at he

end ThomGame.Analysis
