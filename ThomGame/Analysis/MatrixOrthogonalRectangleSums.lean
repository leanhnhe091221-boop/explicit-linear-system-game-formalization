module

public import ThomGame.Analysis.MatrixOrthogonalCornerSums
public import ThomGame.Analysis.MatrixProjectionRankSums
public import ThomGame.Analysis.MatrixALTDiagonalSpectrum
public import ThomGame.Analysis.MatrixMixedNorm

/-!
# Sums of contractions in disjoint rectangles

Orthogonal final supports remove cross Gram terms; orthogonal initial
supports bound their sum by one. A block-preserving linear map has
exactly additive squared Hilbert norms on such a family.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat}

theorem matrixContraction_gram_le_support (Q X : CMatrix d) (hQ : IsStarProjection Q)
    (hr : X * Q = X) (hn : matrixOpNorm X ≤ 1) : star X * X ≤ Q := by
  have hg : star X * X ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg X)).mp
    rw [CStarRing.norm_star_mul_self]
    change matrixOpNorm X * matrixOpNorm X ≤ 1
    nlinarith [matrixOpNorm_nonneg X]
  have hs : Q * star X = star X := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hr
  have hb := hQ.isSelfAdjoint.conjugate_le_conjugate hg
  change Q * (star X * X) * Q ≤ Q * 1 * Q at hb
  rw [← mul_assoc Q (star X) X, hs, mul_assoc, hr, mul_one, hQ.isIdempotentElem.eq] at hb
  exact hb

theorem matrixOrthogonalRectangles_sum_contraction {μ : Type*} [Fintype μ]
    (P Q X : μ → CMatrix d) (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ i, IsStarProjection (Q i))
    (horthP : Pairwise (fun i j => P i * P j = 0))
    (horthQ : Pairwise (fun i j => Q i * Q j = 0))
    (hl : ∀ i, P i * X i = X i) (hr : ∀ i, X i * Q i = X i)
    (hn : ∀ i, matrixOpNorm (X i) ≤ 1) : matrixOpNorm (∑ i, X i) ≤ 1 := by
  have hg : star (∑ i, X i) * (∑ i, X i) ≤ 1 := by
    rw [Matrix.star_eq_conjTranspose, matrixCorner_sum_gram P X hP horthP hl]
    exact (Finset.sum_le_sum (fun i _ => matrixContraction_gram_le_support (Q i) (X i) (hQ i) (hr i) (hn i))).trans
      (matrixProjection_sum Q hQ horthQ).le_one
  have hb := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg (∑ i, X i))).mpr hg
  rw [CStarRing.norm_star_mul_self] at hb
  change matrixOpNorm (∑ i, X i) * matrixOpNorm (∑ i, X i) ≤ 1 at hb
  nlinarith [matrixOpNorm_nonneg (∑ i, X i)]

theorem matrixOrthogonalRectangles_sum_hsNorm_sq {μ : Type*} [Fintype μ]
    (P X : μ → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horthP : Pairwise (fun i j => P i * P j = 0)) (hl : ∀ i, P i * X i = X i) :
    hsNorm (∑ i, X i) ^ 2 = ∑ i, hsNorm (X i) ^ 2 := by
  have horth : Pairwise (fun i j => (X i)ᴴ * X j = 0) := by
    intro i j hij
    have hi : (X i)ᴴ * P i = (X i)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, (hP i).isSelfAdjoint.isHermitian.eq] using
        congrArg Matrix.conjTranspose (hl i)
    exact matrixCorner_cross_mul hi (hl j) (horthP hij)
  simpa only [rectHSNorm_eq_hsNorm] using rectHSNorm_orthogonal_sum_sq d X horth

theorem matrixOrthogonalRectangles_defect_sum {μ : Type*} [Fintype μ]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (P X : μ → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horthP : Pairwise (fun i j => P i * P j = 0)) (hl : ∀ i, P i * X i = X i)
    (hinv : ∀ i Y, P i * Y = Y → P i * F Y = F Y) :
    hsNorm (F (F (∑ i, X i)) - F (∑ i, X i)) ^ 2 = ∑ i, hsNorm (F (F (X i)) - F (X i)) ^ 2 := by
  have hs (i : μ) : P i * (F (F (X i)) - F (X i)) = F (F (X i)) - F (X i) := by
    rw [mul_sub, hinv i _ (hinv i _ (hl i)), hinv i _ (hl i)]
  simpa only [map_sum, ← Finset.sum_sub_distrib] using
    matrixOrthogonalRectangles_sum_hsNorm_sq P (fun i => F (F (X i)) - F (X i)) hP horthP hs

theorem matrixOrthogonalRectangles_defect_sum_le [NeZero d] {μ : Type*} [Fintype μ]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q X : μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ i, IsStarProjection (Q i))
    (horthP : Pairwise (fun i j => P i * P j = 0))
    (horthQ : Pairwise (fun i j => Q i * Q j = 0))
    (hl : ∀ i, P i * X i = X i) (hr : ∀ i, X i * Q i = X i)
    (hn : ∀ i, matrixOpNorm (X i) ≤ 1)
    (hinv : ∀ i Y, P i * Y = Y → P i * F Y = F Y) :
    ∑ i, hsNorm (F (F (X i)) - F (X i)) ^ 2 ≤ matrixMixedNorm (F.comp F - F) ^ 2 := by
  have hc := matrixOrthogonalRectangles_sum_contraction P Q X hP hQ horthP horthQ hl hr hn
  have hb := (hsNorm_apply_le_matrixMixedNorm (F.comp F - F) (∑ i, X i)).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (matrixMixedNorm_nonneg (F.comp F - F)))
  change hsNorm (F (F (∑ i, X i)) - F (∑ i, X i)) ≤ matrixMixedNorm (F.comp F - F) at hb
  rw [← matrixOrthogonalRectangles_defect_sum F P X hP horthP hl hinv]
  exact pow_le_pow_left₀ (hsNorm_nonneg _) hb 2

end ThomGame.Analysis
