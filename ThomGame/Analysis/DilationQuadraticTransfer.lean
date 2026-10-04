module

public import ThomGame.Analysis.FiniteRegularDilation
public import ThomGame.Analysis.StarProjectionPairGap

/-! Transferring a quadratic inequality through an isometry at one test vector. -/

@[expose] public section
namespace ThomGame.Analysis

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_sq_le_of_norm_sub_le (y z : K) {η L : ℝ}
    (hy : ‖y‖ ≤ L) (hz : ‖z‖ ≤ L) (hη : 0 ≤ η) (he : ‖y-z‖ ≤ η) :
    ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 + 2*L*η := by
  have hd := (norm_sub_norm_le y z).trans he
  have hh := mul_le_mul_of_nonneg_right hd (add_nonneg (norm_nonneg y) (norm_nonneg z))
  have hn := mul_le_mul_of_nonneg_right (add_le_add hy hz) hη
  nlinarith

theorem re_inner_sub_le (x y z : K) :
    (inner ℂ x y).re - (inner ℂ x z).re ≤ ‖x‖ * ‖y-z‖ := by
  have hh := (Complex.re_le_norm (inner ℂ x (y-z))).trans (norm_inner_le_norm _ _)
  simpa only [inner_sub_right, Complex.sub_re] using hh

theorem dilation_quadratic_transfer (S : H →ₗᵢ[ℂ] K) (x y : H) (z : K)
    {lam η L : ℝ} (hlam : 0 ≤ lam) (hη : 0 ≤ η)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ L) (hz : ‖z‖ ≤ L)
    (he : ‖z - S y‖ ≤ η)
    (hpoly : lam * (inner ℂ (S x) z).re ≤ ‖z‖ ^ 2) :
    lam * (inner ℂ x y).re ≤ ‖y‖ ^ 2 + (2*L+lam)*η := by
  have hsx : ‖S x‖ ≤ 1 := by simpa using hx
  have hsy : ‖S y‖ ≤ L := by simpa using hy
  have hi := re_inner_sub_le (S x) (S y) z
  have he' : ‖S y-z‖ ≤ η := by simpa only [norm_sub_rev] using he
  have hb := mul_le_mul hsx he' (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  rw [S.inner_map_map] at hi
  have hn := norm_sq_le_of_norm_sub_le z (S y) hz hsy hη he
  simp only [S.norm_map] at hn
  have hl := mul_le_mul_of_nonneg_left (show (inner ℂ x y).re ≤
      (inner ℂ (S x) z).re + η by linarith) hlam
  nlinarith

theorem dilation_projection_energy (S : H →ₗᵢ[ℂ] K) (x y : H) (P : K →L[ℂ] K)
    (hP : IsStarProjection P) {η L : ℝ} (hη : 0 ≤ η)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ L) (hz : ‖P (S x)‖ ≤ L)
    (he : ‖P (S x) - S y‖ ≤ η) :
    ‖y‖ ^ 2 ≤ (inner ℂ x y).re + (2*L+1)*η := by
  have hp : (inner ℂ (S x) (P (S x))).re = ‖P (S x)‖ ^ 2 := by
    have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp hP.nonneg).inner_left_eq_inner_right
      (S x) (P (S x))
    rw [← ContinuousLinearMap.mul_apply, hP.isIdempotentElem.eq] at hh
    rw [← hh]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hn := norm_sq_le_of_norm_sub_le (S y) (P (S x))
    (by simpa using hy) hz hη (by simpa only [norm_sub_rev] using he)
  simp only [S.norm_map] at hn
  have hi := re_inner_sub_le (S x) (P (S x)) (S y)
  rw [S.inner_map_map, hp] at hi
  have hb := mul_le_mul (show ‖S x‖ ≤ 1 by simpa using hx) he
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith

theorem residual_intertwining (S : H →ₗᵢ[ℂ] K) (x y : H) (P : K →L[ℂ] K)
    {η : ℝ} (he : ‖S y - P (S x)‖ ≤ η) :
    ‖(1-P) (S x) - S (x-y)‖ ≤ η := by
  have hid : (1-P) (S x) - S (x-y) = S y - P (S x) := by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    abel
  rwa [hid]

theorem projection_residual_energy_transfer (S : H →ₗᵢ[ℂ] K)
    (x y : H) (P : K →L[ℂ] K) (hP : IsStarProjection P)
    {η : ℝ} (hη : 0 ≤ η) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (he : ‖S y - P (S x)‖ ≤ η) :
    ‖x-y‖ ^ 2 ≤ (inner ℂ x (x-y)).re + 5*η := by
  have hd : ‖x-y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have hz : ‖(1-P) (S x)‖ ≤ 2 := by
    have hn := (1-P).le_opNorm (S x)
    have hb := mul_le_mul (IsStarProjection.norm_le _ hP.one_sub)
      (show ‖S x‖ ≤ 1 by simpa using hx) (norm_nonneg _) zero_le_one
    linarith
  convert dilation_projection_energy S x (x-y) (1-P) hP.one_sub hη hx hd hz
    (residual_intertwining S x y P he) using 1 <;> norm_num

theorem pair_residual_quadratic_transfer (S : H →ₗᵢ[ℂ] K)
    (x y y' : H) (P Q : K →L[ℂ] K) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hpoly : (11/20:ℝ) • ((1-P)+(1-Q)) ≤ ((1-P)+(1-Q))*((1-P)+(1-Q)))
    {η : ℝ} (hη : 0 ≤ η) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hy' : ‖y'‖ ≤ 1)
    (he : ‖S y - P (S x)‖ ≤ η) (he' : ‖S y' - Q (S x)‖ ≤ η) :
    (11/20:ℝ) * (inner ℂ x ((x-y)+(x-y'))).re ≤
      ‖(x-y)+(x-y')‖ ^ 2 + 18*η := by
  let D := (1-P)+(1-Q)
  have hd : 0 ≤ D := add_nonneg hP.one_sub.nonneg hQ.one_sub.nonneg
  have hxs : ‖S x‖ ≤ 1 := by simpa using hx
  have hPn : ‖(1-P) (S x)‖ ≤ 1 := by
    exact ((1-P).le_opNorm (S x)).trans
      (by simpa using mul_le_mul (IsStarProjection.norm_le _ hP.one_sub) hxs (norm_nonneg _) zero_le_one)
  have hQn : ‖(1-Q) (S x)‖ ≤ 1 := by
    exact ((1-Q).le_opNorm (S x)).trans
      (by simpa using mul_le_mul (IsStarProjection.norm_le _ hQ.one_sub) hxs (norm_nonneg _) zero_le_one)
  have hDn : ‖D (S x)‖ ≤ 4 := by
    change ‖(1-P) (S x) + (1-Q) (S x)‖ ≤ 4
    exact (norm_add_le _ _).trans (by linarith)
  have hdn : ‖(x-y)+(x-y')‖ ≤ 4 :=
    (norm_add_le _ _).trans ((add_le_add (norm_sub_le x y) (norm_sub_le x y')).trans (by linarith))
  have herr : ‖D (S x) - S ((x-y)+(x-y'))‖ ≤ 2*η := by
    have hid : D (S x) - S ((x-y)+(x-y')) =
        ((1-P) (S x)-S (x-y)) + ((1-Q) (S x)-S (x-y')) := by
      simp only [D, add_apply, map_add]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add (residual_intertwining S x y P he)
      (residual_intertwining S x y' Q he')).trans_eq (by ring))
  have hpol : (11/20:ℝ) * (inner ℂ (S x) (D (S x))).re ≤ ‖D (S x)‖ ^ 2 := by
    have hh := operator_re_inner_mono hpoly (S x)
    have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hd).inner_left_eq_inner_right (S x) (D (S x))
    have hn : (inner ℂ (S x) ((D*D) (S x))).re = ‖D (S x)‖ ^ 2 := by
      rw [mul_apply_eq_comp, ← hs]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    change (inner ℂ (S x) (((11/20:ℝ) • D) (S x))).re ≤
      (inner ℂ (S x) ((D*D) (S x))).re at hh
    rw [hn] at hh
    simp only [smul_apply] at hh
    rw [← algebraMap_smul ℂ (11/20:ℝ), RCLike.algebraMap_eq_ofReal, inner_smul_right] at hh
    norm_num [Complex.mul_re] at hh
    exact hh
  have ht := dilation_quadratic_transfer S x ((x-y)+(x-y')) (D (S x))
    (by norm_num : (0:ℝ) ≤ 11/20) (by positivity : 0 ≤ 2*η) hx hdn hDn herr hpol
  nlinarith

end ThomGame.Analysis
