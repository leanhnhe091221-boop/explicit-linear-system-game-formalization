module

public import ThomGame.Analysis.HilbertUnitaryInvariants
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Coercive complex Hilbert operators have closed range and are bijective. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem hilbert_coercive_norm_lower (T : H →L[ℂ] H) (a : ℝ)
    (hT : ∀ x : H, a * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re) (x : H) : a * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn := norm_pos_iff.mpr hx
  have h := (hT x).trans (re_inner_le_norm (𝕜 := ℂ) x (T x))
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

omit [CompleteSpace H] in
theorem hilbert_coercive_antilipschitz (T : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hT : ∀ x : H, a * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re) :
    AntilipschitzWith (Real.toNNReal a⁻¹) T := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr ha.le)]
  have h := hilbert_coercive_norm_lower T a hT x
  have hi : ‖x‖ ≤ ‖T x‖ / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_inv_mul] using hi

theorem hilbert_coercive_closed_range (T : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hT : ∀ x : H, a * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re) : IsClosed (T.range : Set H) :=
  (hilbert_coercive_antilipschitz T a ha hT).isClosed_range T.uniformContinuous

theorem hilbert_coercive_range_eq_top (T : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hT : ∀ x : H, a * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re) : T.range = ⊤ := by
  let := (hilbert_coercive_closed_range T a ha hT).completeSpace_coe
  rw [← T.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro x
  apply (Submodule.mem_orthogonal _ _).mpr
  intro w hw
  have hwinner : inner ℂ (T w) w = 0 := (Submodule.mem_orthogonal _ _).mp hw (T w) ⟨w, rfl⟩
  have h := hT w
  have hreal : (inner ℂ w (T w)).re = 0 := by
    rw [← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex, hwinner, Complex.zero_re]
  rw [hreal] at h
  have hnorm : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖]
  have hwzero : w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [hwzero, inner_zero_left]

theorem hilbert_coercive_bijective (T : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hT : ∀ x : H, a * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re) : Function.Bijective T :=
  ⟨(hilbert_coercive_antilipschitz T a ha hT).injective,
    LinearMap.range_eq_top.mp (hilbert_coercive_range_eq_top T a ha hT)⟩

end ThomGame.Analysis
