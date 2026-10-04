module

public import ThomGame.Analysis.CStarNormLift

/-!
# Exact norm bounds for arbitrary C-star algebra lifts

Right multiplication by a continuous function of `a* a` clips singular
values at the prescribed positive bound. Unlike decomposition into real
and imaginary parts, this construction loses no factor in the norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped CStarAlgebra

noncomputable def realRightNormFactor (K t : ℝ) : ℝ := K / Real.sqrt (max (K ^ 2) t)

theorem realRightNormFactor_continuous (K : ℝ) (hK : 0 < K) : Continuous (realRightNormFactor K) := by
  apply Continuous.div continuous_const (Real.continuous_sqrt.comp (continuous_const.max continuous_id))
  intro t
  exact ne_of_gt (Real.sqrt_pos.2 ((sq_pos_of_pos hK).trans_le (le_max_left _ _)))

theorem realRightNormFactor_eq_one (K t : ℝ) (hK : 0 < K) (ht : t ≤ K ^ 2) :
    realRightNormFactor K t = 1 := by
  rw [realRightNormFactor, max_eq_left ht, Real.sqrt_sq hK.le, div_self hK.ne']

theorem realRightNormFactor_square_bound (K t : ℝ) (hK : 0 < K) (ht : 0 ≤ t) :
    ‖realRightNormFactor K t * t * realRightNormFactor K t‖ ≤ K ^ 2 := by
  have hm : 0 < max (K ^ 2) t := (sq_pos_of_pos hK).trans_le (le_max_left _ _)
  have he : realRightNormFactor K t * t * realRightNormFactor K t = K ^ 2 * t / max (K ^ 2) t := by
    calc
      _ = K ^ 2 * t / Real.sqrt (max (K ^ 2) t) ^ 2 := by
        unfold realRightNormFactor
        ring
      _ = _ := by rw [Real.sq_sqrt hm.le]
  rw [he, Real.norm_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg K) ht) hm.le)]
  exact (div_le_iff₀ hm).mpr (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg K))

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

noncomputable def cstarRightNormClamp (K : ℝ) (a : A) : A :=
  a * cfc (realRightNormFactor K) (star a * a)

theorem cstarRightNormClamp_gram (K : ℝ) (hK : 0 < K) (a : A) :
    star (cstarRightNormClamp K a) * cstarRightNormClamp K a =
      cfc (fun t => realRightNormFactor K t * t * realRightNormFactor K t) (star a * a) := by
  have hc : ContinuousOn (realRightNormFactor K) (spectrum ℝ (star a * a)) :=
    (realRightNormFactor_continuous K hK).continuousOn
  have hs : IsSelfAdjoint (cfc (realRightNormFactor K) (star a * a)) := IsSelfAdjoint.cfc
  rw [cfc_mul (fun t : ℝ => realRightNormFactor K t * t) (realRightNormFactor K) (star a * a)
      (hc.mul continuous_id.continuousOn) hc,
    cfc_mul (realRightNormFactor K) (fun t : ℝ => t) (star a * a) hc continuous_id.continuousOn,
    cfc_id' ℝ _ (IsSelfAdjoint.star_mul_self a)]
  unfold cstarRightNormClamp
  rw [star_mul, hs.star_eq]
  simp only [mul_assoc]

theorem cstarRightNormClamp_norm_le (K : ℝ) (hK : 0 < K) (a : A) : ‖cstarRightNormClamp K a‖ ≤ K := by
  apply (sq_le_sq₀ (norm_nonneg _) hK.le).mp
  rw [sq, ← CStarRing.norm_star_mul_self, cstarRightNormClamp_gram K hK]
  exact norm_cfc_le (sq_nonneg K) (fun t ht => realRightNormFactor_square_bound K t hK
    (spectrum_star_mul_self_nonneg t ht))

theorem cstarRightNormClamp_eq_self (K : ℝ) (hK : 0 < K) (a : A) (ha : ‖a‖ ≤ K) :
    cstarRightNormClamp K a = a := by
  have he : cfc (realRightNormFactor K) (star a * a) = (1 : A) := by
    calc
      _ = cfc (fun _ : ℝ => 1) (star a * a) := by
        apply cfc_congr
        intro t ht
        apply realRightNormFactor_eq_one K t hK
        have hb := IsometricContinuousFunctionalCalculus.norm_spectrum_le (star a * a) ht
          (IsSelfAdjoint.star_mul_self a)
        rw [Real.norm_of_nonneg (spectrum_star_mul_self_nonneg t ht),
          CStarRing.norm_star_mul_self] at hb
        exact hb.trans (by simpa only [sq] using (sq_le_sq₀ (norm_nonneg a) hK.le).mpr ha)
      _ = 1 := cfc_const_one ℝ _ (IsSelfAdjoint.star_mul_self a)
  rw [cstarRightNormClamp, he, mul_one]

theorem map_cstarRightNormClamp (φ : A →⋆ₐ[ℂ] B) (K : ℝ) (hK : 0 < K) (a : A) :
    φ (cstarRightNormClamp K a) = cstarRightNormClamp K (φ a) := by
  unfold cstarRightNormClamp
  rw [map_mul, φ.map_cfc (realRightNormFactor K) (star a * a)
    (realRightNormFactor_continuous K hK).continuousOn (map_continuous φ)
    (IsSelfAdjoint.star_mul_self a) ((IsSelfAdjoint.star_mul_self a).map φ), map_mul, map_star]

theorem exists_cstar_exact_norm_lift (φ : A →⋆ₐ[ℂ] B) (a : A) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ‖φ a‖ ≤ K) : ∃ b : A, ‖b‖ ≤ K ∧ φ b = φ a := by
  obtain rfl | hK := hK.eq_or_lt
  · refine ⟨0, by simp, ?_⟩
    rw [map_zero]
    exact (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))).symm
  · refine ⟨cstarRightNormClamp K a, cstarRightNormClamp_norm_le K hK a, ?_⟩
    rw [map_cstarRightNormClamp φ K hK a, cstarRightNormClamp_eq_self K hK (φ a) hbound]

end ThomGame.Analysis
