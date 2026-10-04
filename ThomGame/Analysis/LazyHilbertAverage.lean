module

public import ThomGame.Analysis.PositiveOperatorEstimates

/-!
# Lazy symmetric averages of Hilbert-space isometries

The averaging weights are exactly those in ALT. The quadratic form of
the average and of its complement are sums of squared norms. Thus the
average is a positive self-adjoint contraction, and its fixed vectors
are exactly the common fixed vectors of the given isometries.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

noncomputable def lazyMarkovWeight (h : Nat) : ℝ := (4 * (h : ℝ))⁻¹

theorem lazyMarkovWeight_nonneg (h : Nat) : 0 ≤ lazyMarkovWeight h :=
  inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg h))

theorem lazyMarkovWeight_pos (h : Nat) [NeZero h] : 0 < lazyMarkovWeight h :=
  inv_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos h)))

theorem lazyMarkovWeight_mul_card (h : Nat) [NeZero h] : lazyMarkovWeight h * h = 1 / 4 := by
  unfold lazyMarkovWeight
  have hh : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  field_simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {h : Nat} [NeZero h] (V : Fin h → H ≃ₗᵢ[ℂ] H)

noncomputable def lazyHilbertAverage : H →L[ℂ] H :=
  (((1 / 2 : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ H +
    (lazyMarkovWeight h : ℂ) • ∑ j,
      ((V j).toLinearIsometry.toContinuousLinearMap + (V j).symm.toLinearIsometry.toContinuousLinearMap)

omit [NeZero h] in
@[simp] theorem lazyHilbertAverage_apply (ξ : H) :
    lazyHilbertAverage V ξ = ((1 / 2 : ℝ) : ℂ) • ξ +
      (lazyMarkovWeight h : ℂ) • ∑ j, (V j ξ + (V j).symm ξ) := by
  simp only [lazyHilbertAverage, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    sum_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

theorem lazyHilbertAverage_norm_apply_le (ξ : H) : ‖lazyHilbertAverage V ξ‖ ≤ ‖ξ‖ := by
  have hsum : ‖∑ j, (V j ξ + (V j).symm ξ)‖ ≤ (h : ℝ) * (2 * ‖ξ‖) := by
    calc
      _ ≤ ∑ j, ‖V j ξ + (V j).symm ξ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin h, (2 * ‖ξ‖) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [LinearIsometryEquiv.norm_map, two_mul] using norm_add_le (V j ξ) ((V j).symm ξ)
      _ = _ := by simp
  rw [lazyHilbertAverage_apply]
  calc
    _ ≤ ‖((1 / 2 : ℝ) : ℂ) • ξ‖ + ‖(lazyMarkovWeight h : ℂ) • ∑ j, (V j ξ + (V j).symm ξ)‖ := norm_add_le _ _
    _ = 1 / 2 * ‖ξ‖ + lazyMarkovWeight h * ‖∑ j, (V j ξ + (V j).symm ξ)‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (lazyMarkovWeight_nonneg h)]
    _ ≤ 1 / 2 * ‖ξ‖ + lazyMarkovWeight h * ((h : ℝ) * (2 * ‖ξ‖)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hsum (lazyMarkovWeight_nonneg h)) _
    _ = ‖ξ‖ := by rw [← mul_assoc, lazyMarkovWeight_mul_card]; ring

theorem lazyHilbertAverage_norm_le : ‖lazyHilbertAverage V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun ξ => by simpa only [one_mul] using lazyHilbertAverage_norm_apply_le V ξ)

omit [NeZero h] in
theorem lazyHilbertAverage_symmetric : (lazyHilbertAverage V).IsSymmetric := by
  intro ξ η
  change inner ℂ (lazyHilbertAverage V ξ) η = inner ℂ ξ (lazyHilbertAverage V η)
  simp only [lazyHilbertAverage_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, sum_inner, inner_sum, Complex.conj_ofReal]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm, add_comm]

theorem isometry_pair_re_inner (W : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    (inner ℂ ξ (W ξ)).re + (inner ℂ ξ (W.symm ξ)).re = 2 * (inner ℂ (W ξ) ξ).re := by
  rw [← W.inner_map_eq_flip ξ ξ]
  have he : (inner ℂ ξ (W ξ)).re = (inner ℂ (W ξ) ξ).re := inner_re_symm (𝕜 := ℂ) ξ (W ξ)
  rw [he, two_mul]

omit [NeZero h] in
theorem lazyHilbertAverage_quadratic (ξ : H) :
    (inner ℂ ξ (lazyHilbertAverage V ξ)).re = 1 / 2 * ‖ξ‖ ^ 2 +
      lazyMarkovWeight h * ∑ j, ((inner ℂ ξ (V j ξ)).re + (inner ℂ ξ ((V j).symm ξ)).re) := by
  simp only [lazyHilbertAverage_apply, inner_add_right, inner_smul_right,
    inner_sum, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [show (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) ξ]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.add_re]

theorem isometry_pair_norm_add_sq (W : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    ‖W ξ + ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 +
      ((inner ℂ ξ (W ξ)).re + (inner ℂ ξ (W.symm ξ)).re) := by
  rw [isometry_pair_re_inner]
  have hn := norm_add_sq (𝕜 := ℂ) (W ξ) ξ
  simp only [W.norm_map, RCLike.re_to_complex] at hn
  linarith

theorem isometry_pair_norm_sub_sq (W : H ≃ₗᵢ[ℂ] H) (ξ : H) :
    ‖W ξ - ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 -
      ((inner ℂ ξ (W ξ)).re + (inner ℂ ξ (W.symm ξ)).re) := by
  rw [isometry_pair_re_inner]
  have hn := norm_sub_sq (𝕜 := ℂ) (W ξ) ξ
  simp only [W.norm_map, RCLike.re_to_complex] at hn
  linarith

theorem lazyHilbertAverage_positive_form (ξ : H) :
    (inner ℂ ξ (lazyHilbertAverage V ξ)).re = lazyMarkovWeight h * ∑ j, ‖V j ξ + ξ‖ ^ 2 := by
  rw [lazyHilbertAverage_quadratic]
  simp_rw [isometry_pair_norm_add_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_add]
  rw [← mul_assoc (lazyMarkovWeight h) (h : ℝ), lazyMarkovWeight_mul_card]
  ring

theorem lazyHilbertAverage_energy (ξ : H) :
    (inner ℂ ξ (ξ - lazyHilbertAverage V ξ)).re = lazyMarkovWeight h * ∑ j, ‖V j ξ - ξ‖ ^ 2 := by
  rw [inner_sub_right, Complex.sub_re, lazyHilbertAverage_quadratic,
    show (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) ξ]
  simp_rw [isometry_pair_norm_sub_sq]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_sub, ← mul_assoc, lazyMarkovWeight_mul_card]
  ring

theorem lazyHilbertAverage_nonneg : 0 ≤ lazyHilbertAverage V := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨lazyHilbertAverage_symmetric V, fun ξ => ?_⟩
  change 0 ≤ (inner ℂ (lazyHilbertAverage V ξ) ξ).re
  rw [show (inner ℂ (lazyHilbertAverage V ξ) ξ).re =
      (inner ℂ ξ (lazyHilbertAverage V ξ)).re from inner_re_symm (𝕜 := ℂ) _ _,
    lazyHilbertAverage_positive_form]
  exact mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem lazyHilbertAverage_le_one : lazyHilbertAverage V ≤ 1 := by
  apply ContinuousLinearMap.le_def.mpr
  refine ⟨?_, fun ξ => ?_⟩
  · exact (ContinuousLinearMap.isPositive_id (𝕜 := ℂ) (E := H)).isSymmetric.sub
      (lazyHilbertAverage_symmetric V)
  · change 0 ≤ (inner ℂ (ξ - lazyHilbertAverage V ξ) ξ).re
    rw [show (inner ℂ (ξ - lazyHilbertAverage V ξ) ξ).re =
        (inner ℂ ξ (ξ - lazyHilbertAverage V ξ)).re from inner_re_symm (𝕜 := ℂ) _ _,
      lazyHilbertAverage_energy]
    exact mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem lazyHilbertAverage_fixed_iff (ξ : H) :
    lazyHilbertAverage V ξ = ξ ↔ ∀ j, V j ξ = ξ := by
  constructor
  · intro hfix
    have he := lazyHilbertAverage_energy V ξ
    rw [hfix, sub_self, inner_zero_right, Complex.zero_re] at he
    have hs : (∑ j, ‖V j ξ - ξ‖ ^ 2) = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt (lazyMarkovWeight_pos h))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖V j ξ - ξ‖)).mp hs
    intro j
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (hz j (Finset.mem_univ j))))
  · intro hfix
    have hinv (j : Fin h) : (V j).symm ξ = ξ := by
      apply (V j).injective
      rw [(V j).apply_symm_apply, hfix j]
    have hsum : (∑ j, (V j ξ + (V j).symm ξ)) = (2 * (h : ℂ)) • ξ := by
      simp only [hfix, hinv, ← two_smul ℂ ξ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    rw [lazyHilbertAverage_apply, hsum, smul_smul, ← add_smul]
    have hw : ((1 / 2 : ℝ) : ℂ) + (lazyMarkovWeight h : ℂ) * (2 * (h : ℂ)) = 1 := by
      have hr : (1 / 2 : ℝ) + lazyMarkovWeight h * (2 * (h : ℝ)) = 1 := by
        nlinarith [lazyMarkovWeight_mul_card h]
      exact_mod_cast hr
    rw [hw, one_smul]

variable [CompleteSpace H]

theorem lazyHilbertAverage_defect_norm_sq_le (ξ : H) :
    ‖ξ - lazyHilbertAverage V ξ‖ ^ 2 ≤ (inner ℂ ξ (ξ - lazyHilbertAverage V ξ)).re := by
  have hp : 0 ≤ (1 : H →L[ℂ] H) - lazyHilbertAverage V := sub_nonneg.mpr (lazyHilbertAverage_le_one V)
  have hn : ‖(1 : H →L[ℂ] H) - lazyHilbertAverage V‖ ≤ 1 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one hp).mpr
    rw [map_one]
    exact sub_le_self _ (lazyHilbertAverage_nonneg V)
  simpa only [sub_apply, one_apply_eq_self, one_mul] using
    positive_operator_apply_norm_sq_le ((1 : H →L[ℂ] H) - lazyHilbertAverage V) hp 1 zero_le_one hn ξ

end ThomGame.Analysis
