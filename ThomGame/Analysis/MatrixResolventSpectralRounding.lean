module

public import ThomGame.Analysis.MatrixSpectralRoundingTrace
public import ThomGame.Analysis.MatrixResolventCoverage

/-!
# Actual spectral rounding of the resolvent family

Each rounded projection has the required rank bound. Its positive-part
rounding error is bounded using the rank of the original projection,
and its weighted trace is controlled by the actual resolvent estimate.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {lam s γ : ℝ} {S₀ : CMatrix d}

theorem normalizedTrace_real_smul (c : ℝ) (X : CMatrix d) :
    (normalizedTrace (c • X)).re = c * (normalizedTrace X).re := by
  change (normalizedTrace ((c : ℂ) • X)).re = _
  rw [normalizedTrace_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

noncomputable def matrixResolventSpectralProjection (lam : ℝ) (S₀ : CMatrix d)
    (F : Nat → CMatrix d) (s : ℝ) (i : Nat) : CMatrix d :=
  matrixSpectralCut (matrixResolventDifferenceFamily lam S₀ F i) s

theorem matrixResolventSpectralProjection_isStarProjection (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (s : ℝ) (i : Nat) :
    IsStarProjection (matrixResolventSpectralProjection lam S₀ F s i) :=
  matrixSpectralCut_isStarProjection
    (matrixResolventDifferenceFamily_nonneg hlam hS₀ F hF i).isSelfAdjoint.isHermitian s

theorem matrixResolventSpectralProjection_rank_le (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (hs : 0 < s) (i : Nat) :
    (matrixResolventSpectralProjection lam S₀ F s i).rank ≤ (F i).rank :=
  (matrixSpectralCut_rank_le
    (matrixResolventDifferenceFamily_nonneg hlam hS₀ F hF i).isSelfAdjoint.isHermitian hs).trans
    (matrixProjectionResolventDifference_rank_le hlam (matrixProjectionPartialSum_nonneg hS₀ F hF i) (hF i))

theorem matrixResolventSpectralProjection_rounding_trace_le (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (hs : 0 ≤ s) (i : Nat) :
    (normalizedTrace (matrixResolventDifferenceFamily lam S₀ F i -
      matrixResolventSpectralProjection lam S₀ F s i)⁺).re ≤ s * (normalizedTrace (F i)).re := by
  have hi := matrixProjectionPartialSum_nonneg hS₀ F hF i
  exact matrix_spectral_rounding_posPart_trace_le_projection
    (matrixProjectionResolventDifference_nonneg hlam hi (hF i))
    (matrixProjectionResolventDifference_le_one hlam hi (hF i)) (hF i)
    (matrixProjectionResolventDifference_rank_le hlam hi (hF i)) hs

theorem matrixResolventSpectralProjection_rounding_sum_le (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (hs : 0 ≤ s) (n : Nat) :
    (∑ i : Fin n, (normalizedTrace (matrixResolventDifferenceFamily lam S₀ F i -
      matrixResolventSpectralProjection lam S₀ F s i)⁺).re) ≤
      s * ∑ i ∈ Finset.range n, (normalizedTrace (F i)).re := by
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => matrixResolventSpectralProjection_rounding_trace_le hlam hS₀ F hF hs i

theorem matrixResolventSpectralProjection_weighted_trace_le (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (hs : 0 < s) (i : Nat) :
    (normalizedTrace (matrixProjectionPartialSum S₀ F i ^ 2 *
      matrixResolventSpectralProjection lam S₀ F s i)).re ≤
      (s⁻¹ * lam) * (normalizedTrace (F i)).re := by
  have hi := matrixProjectionPartialSum_nonneg hS₀ F hF i
  have hsquare : 0 ≤ matrixProjectionPartialSum S₀ F i ^ 2 := by
    simpa only [hi.isSelfAdjoint.star_eq, sq] using star_mul_self_nonneg (matrixProjectionPartialSum S₀ F i)
  calc
    _ ≤ (normalizedTrace (matrixProjectionPartialSum S₀ F i ^ 2 *
        (s⁻¹ • matrixResolventDifferenceFamily lam S₀ F i))).re :=
      normalizedTrace_mul_re_mono hsquare
        (matrixSpectralCut_le_scaled (matrixResolventDifferenceFamily_nonneg hlam hS₀ F hF i) hs)
    _ = s⁻¹ * (normalizedTrace (matrixProjectionPartialSum S₀ F i ^ 2 *
        matrixResolventDifferenceFamily lam S₀ F i)).re := by
      rw [mul_smul_comm, normalizedTrace_real_smul]
    _ ≤ s⁻¹ * (lam * (normalizedTrace (F i)).re) :=
      mul_le_mul_of_nonneg_left
        (matrixProjectionResolventDifference_weighted_trace_le hlam hi (hF i)) (inv_nonneg.mpr hs.le)
    _ = _ := by ring

theorem matrixResolventSpectralProjection_weighted_trace_sum_le (hlam : 0 < lam) (hS₀ : 0 ≤ S₀)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (hs : 0 < s) (n : Nat) :
    (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum S₀ F i ^ 2 *
      matrixResolventSpectralProjection lam S₀ F s i)).re) ≤
      (s⁻¹ * lam) * ∑ i ∈ Finset.range n, (normalizedTrace (F i)).re := by
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => matrixResolventSpectralProjection_weighted_trace_le hlam hS₀ F hF hs i

end ThomGame.Analysis
