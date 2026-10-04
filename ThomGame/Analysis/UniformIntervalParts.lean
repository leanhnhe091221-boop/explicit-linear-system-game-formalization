module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Integration by parts for the uniform interval

The boundary weight 1-s squared vanishes at both endpoints. The
identity is for actual Lebesgue interval integrals on [-1,1].
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory

theorem uniform_interval_integration_by_parts {f f' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') :
    (∫ s in (-1 : ℝ)..1, s * f s) =
      (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * f' s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have hg : Continuous (fun s : ℝ => 1 - s ^ 2) := by fun_prop
  have hg' : Continuous (fun s : ℝ => -2 * s) := by fun_prop
  have hd (s : ℝ) : HasDerivAt (fun a : ℝ => 1 - a ^ 2) (-2 * s) s := by
    simpa [id_eq, Pi.pow_apply, neg_mul] using ((hasDerivAt_id s).pow 2).const_sub (1 : ℝ)
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) hg.continuousOn hfc.continuousOn
    (fun s _ => hd s) (fun s _ => hf s) (hg'.intervalIntegrable _ _) (hf'.intervalIntegrable _ _)
  have hi : (∫ s in (-1 : ℝ)..1, (-2 * s) * f s) =
      (-2 : ℝ) * ∫ s in (-1 : ℝ)..1, s * f s := by
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
  rw [hi] at he
  norm_num at he
  linarith

end ThomGame.Analysis
