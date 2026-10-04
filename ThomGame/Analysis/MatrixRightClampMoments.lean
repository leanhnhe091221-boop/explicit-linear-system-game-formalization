module

public import ThomGame.Analysis.CStarContractiveLift
public import ThomGame.Analysis.MatrixUCPCornerMoments
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Fourth-moment control of actual singular-value truncation

The right functional-calculus clamp preserves a rectangular support.
Its tail is bounded by the fourth moment in the original ambient
normalized trace. No singular-value decomposition is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem realRightNormFactor_mem_Icc (K t : ℝ) (hK : 0 < K) :
    0 ≤ realRightNormFactor K t ∧ realRightNormFactor K t ≤ 1 := by
  have hm : 0 < max (K ^ 2) t := (sq_pos_of_pos hK).trans_le (le_max_left _ _)
  have hs : K ≤ Real.sqrt (max (K ^ 2) t) := by
    calc
      K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt (max (K ^ 2) t) := Real.sqrt_le_sqrt (le_max_left _ _)
  exact ⟨div_nonneg hK.le (Real.sqrt_nonneg _),
    (div_le_one (Real.sqrt_pos.mpr hm)).mpr hs⟩

theorem realRightNormFactor_tail_fourth (K t : ℝ) (hK : 0 < K) (ht : 0 ≤ t) :
    K ^ 2 * ((1 - realRightNormFactor K t) * t * (1 - realRightNormFactor K t)) ≤ t ^ 2 := by
  by_cases h : t ≤ K ^ 2
  · rw [realRightNormFactor_eq_one K t hK h]
    simpa using sq_nonneg t
  · obtain ⟨h0, h1⟩ := realRightNormFactor_mem_Icc K t hK
    have hq : (1 - realRightNormFactor K t) ^ 2 ≤ 1 := by nlinarith
    calc
      _ = K ^ 2 * t * (1 - realRightNormFactor K t) ^ 2 := by ring
      _ ≤ K ^ 2 * t := by nlinarith [mul_nonneg (sq_nonneg K) ht]
      _ ≤ t ^ 2 := by nlinarith [le_of_not_ge h]

variable {d : Nat}

theorem matrixRightNormClamp_tail_gram (K : ℝ) (X : CMatrix d) :
    star (X - cstarRightNormClamp K X) * (X - cstarRightNormClamp K X) =
      cfc (fun t : ℝ => (1 - realRightNormFactor K t) * t *
        (1 - realRightNormFactor K t)) (star X * X) := by
  let A := star X * X
  have hA : IsSelfAdjoint A := IsSelfAdjoint.star_mul_self X
  have hC : cfc (fun t : ℝ => 1 - realRightNormFactor K t) A =
      1 - cfc (realRightNormFactor K) A := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA]
  have hCs : IsSelfAdjoint (cfc (fun t : ℝ => 1 - realRightNormFactor K t) A) :=
    cfc_predicate _ _
  have he : X - cstarRightNormClamp K X =
      X * cfc (fun t : ℝ => 1 - realRightNormFactor K t) A := by
    rw [hC, mul_sub, mul_one]
    rfl
  rw [he, star_mul, hCs.star_eq]
  rw [cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_id' ℝ A hA]
  simp only [A, mul_assoc]

theorem matrixRightNormClamp_tail_fourth (K : ℝ) (hK : 0 < K) (X : CMatrix d) :
    K ^ 2 * hsNorm (X - cstarRightNormClamp K X) ^ 2 ≤ hsNorm (star X * X) ^ 2 := by
  let A := star X * X
  have hA : IsSelfAdjoint A := IsSelfAdjoint.star_mul_self X
  have ho : K ^ 2 • (star (X - cstarRightNormClamp K X) * (X - cstarRightNormClamp K X)) ≤ A ^ 2 := by
    rw [matrixRightNormClamp_tail_gram]
    change K ^ 2 • cfc (fun t : ℝ => (1 - realRightNormFactor K t) * t *
      (1 - realRightNormFactor K t)) A ≤ A ^ 2
    rw [← cfc_const_mul (K ^ 2) _ A (A.finite_real_spectrum.continuousOn _),
      ← cfc_pow_id (R := ℝ) A 2 hA]
    apply (cfc_le_iff _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _) hA).mpr
    intro t ht
    exact realRightNormFactor_tail_fourth K t hK (spectrum_star_mul_self_nonneg t ht)
  have ht := normalizedTrace_re_mono ho
  have hg : (normalizedTrace (A ^ 2)).re = hsNorm A ^ 2 := by
    simpa only [hA.star_eq, pow_two, Complex.ofReal_re] using congrArg Complex.re (normalizedTrace_gram A)
  change (normalizedTrace (((K ^ 2 : ℝ) : ℂ) •
    (star (X - cstarRightNormClamp K X) * (X - cstarRightNormClamp K X)))).re ≤ _ at ht
  simpa only [normalizedTrace_smul, normalizedTrace_gram, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hg] using ht

theorem matrixRightNormClamp_rectangle (K : ℝ) (P Q X : CMatrix d)
    (hQ : IsSelfAdjoint Q) (hl : P * X = X) (hr : X * Q = X) :
    P * cstarRightNormClamp K X = cstarRightNormClamp K X ∧
      cstarRightNormClamp K X * Q = cstarRightNormClamp K X := by
  have hs : Q * star X = star X := by
    simpa only [star_mul, hQ.star_eq] using congrArg star hr
  have hc : Commute (star X * X) Q := by
    show (star X * X) * Q = Q * (star X * X)
    rw [mul_assoc, hr, ← mul_assoc Q, hs]
  have hf := (hc.cfc_real (realRightNormFactor K)).eq
  constructor
  · rw [cstarRightNormClamp, ← mul_assoc, hl]
  · rw [cstarRightNormClamp, mul_assoc, hf, ← mul_assoc, hr]

end ThomGame.Analysis
