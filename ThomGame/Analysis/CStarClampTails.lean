module

public import ThomGame.Analysis.CStarNormLift
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The positive and negative tails removed by self-adjoint clipping

The removed part is a difference of two positive elements. Multiplication
by the clipped element acts on these tails as the endpoint scalars.
-/

@[expose] public section
namespace ThomGame.Analysis

def realUpperTail (K t : ℝ) := max (t - K) 0
def realLowerTail (K t : ℝ) := max (-t - K) 0

theorem realUpperTail_continuous (K : ℝ) : Continuous (realUpperTail K) := by
  unfold realUpperTail
  fun_prop

theorem realLowerTail_continuous (K : ℝ) : Continuous (realLowerTail K) := by
  unfold realLowerTail
  fun_prop

theorem realNormClamp_tail_sub (K : ℝ) (hK : 0 ≤ K) (t : ℝ) :
    t - realNormClamp K t = realUpperTail K t - realLowerTail K t := by
  unfold realNormClamp realUpperTail realLowerTail
  grind

theorem realUpperTail_mul_clamp (K : ℝ) (hK : 0 ≤ K) (t : ℝ) :
    realUpperTail K t * realNormClamp K t = K * realUpperTail K t := by
  unfold realNormClamp realUpperTail
  by_cases h : t ≤ K
  · rw [max_eq_right (by linarith : t - K ≤ 0)]
    simp
  · rw [min_eq_left (by linarith : K ≤ t), max_eq_right (by linarith : -K ≤ K)]
    ring

theorem realLowerTail_mul_clamp (K : ℝ) (hK : 0 ≤ K) (t : ℝ) :
    realLowerTail K t * realNormClamp K t = (-K) * realLowerTail K t := by
  unfold realNormClamp realLowerTail
  by_cases h : -K ≤ t
  · rw [max_eq_right (by linarith : -t - K ≤ 0)]
    simp
  · rw [min_eq_right (by linarith : t ≤ K), max_eq_left (by linarith : t ≤ -K)]
    ring

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def cstarUpperTail (K : ℝ) (a : A) := cfc (realUpperTail K) a
noncomputable def cstarLowerTail (K : ℝ) (a : A) := cfc (realLowerTail K) a

theorem cstarUpperTail_nonneg (K : ℝ) (a : A) : 0 ≤ cstarUpperTail K a :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

theorem cstarLowerTail_nonneg (K : ℝ) (a : A) : 0 ≤ cstarLowerTail K a :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

omit [PartialOrder A] [StarOrderedRing A] in
theorem cstarNormClamp_tail_sub (K : ℝ) (hK : 0 ≤ K) (a : A) (ha : IsSelfAdjoint a) :
    a - cstarNormClamp K a = cstarUpperTail K a - cstarLowerTail K a := by
  change a - cfc (realNormClamp K) a = cfc (realUpperTail K) a - cfc (realLowerTail K) a
  rw [← cfc_sub (realUpperTail K) (realLowerTail K) a
    (realUpperTail_continuous K).continuousOn (realLowerTail_continuous K).continuousOn]
  calc
    a - cfc (realNormClamp K) a = cfc (fun t : ℝ => t - realNormClamp K t) a := by
      rw [cfc_sub (fun t : ℝ => t) (realNormClamp K) a continuous_id.continuousOn
        (realNormClamp_continuous K).continuousOn, cfc_id' ℝ a ha]
    _ = _ := cfc_congr (fun t _ => realNormClamp_tail_sub K hK t)

omit [PartialOrder A] [StarOrderedRing A] in
theorem cstarUpperTail_mul_clamp (K : ℝ) (hK : 0 ≤ K) (a : A) :
    cstarUpperTail K a * cstarNormClamp K a = K • cstarUpperTail K a := by
  change cfc (realUpperTail K) a * cfc (realNormClamp K) a = K • cfc (realUpperTail K) a
  rw [← cfc_mul (realUpperTail K) (realNormClamp K) a
    (realUpperTail_continuous K).continuousOn (realNormClamp_continuous K).continuousOn,
    ← cfc_const_mul K (realUpperTail K) a (realUpperTail_continuous K).continuousOn]
  exact cfc_congr (fun t _ => realUpperTail_mul_clamp K hK t)

omit [PartialOrder A] [StarOrderedRing A] in
theorem cstarLowerTail_mul_clamp (K : ℝ) (hK : 0 ≤ K) (a : A) :
    cstarLowerTail K a * cstarNormClamp K a = (-K) • cstarLowerTail K a := by
  change cfc (realLowerTail K) a * cfc (realNormClamp K) a = (-K) • cfc (realLowerTail K) a
  rw [← cfc_mul (realLowerTail K) (realNormClamp K) a
    (realLowerTail_continuous K).continuousOn (realNormClamp_continuous K).continuousOn,
    ← cfc_const_mul (-K) (realLowerTail K) a (realLowerTail_continuous K).continuousOn]
  exact cfc_congr (fun t _ => realLowerTail_mul_clamp K hK t)

end ThomGame.Analysis
