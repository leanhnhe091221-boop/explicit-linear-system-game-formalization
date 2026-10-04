module

public import ThomGame.Analysis.StarProjectionPairGap
public import ThomGame.Analysis.ProjectionSumEnergy
public import ThomGame.Analysis.PositivePolynomialGap
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.BigOperators.Fin

/-! The three-subspace spectral gap, obtained by adding the three pair inequalities. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem threeStarProjections_polynomial {A B C : H →L[ℂ] H}
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hC : IsStarProjection C)
    (c : ℝ)
    (hAB : (1 - c) • (A + B) ≤ (A + B) * (A + B))
    (hBC : (1 - c) • (B + C) ≤ (B + C) * (B + C))
    (hCA : (1 - c) • (C + A) ≤ (C + A) * (C + A)) :
    (1 - 2 * c) • (A + B + C) ≤ (A + B + C) * (A + B + C) := by
  have hp := add_nonneg (add_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hBC)) (sub_nonneg.mpr hCA)
  have he : ((A + B) * (A + B) - (1 - c) • (A + B)) +
      ((B + C) * (B + C) - (1 - c) • (B + C)) +
      ((C + A) * (C + A) - (1 - c) • (C + A)) =
      (A + B + C) * (A + B + C) - (1 - 2 * c) • (A + B + C) := by
    simp only [add_mul, mul_add, hA.isIdempotentElem.eq, hB.isIdempotentElem.eq,
      hC.isIdempotentElem.eq, sub_smul, one_smul, mul_smul, smul_add, two_smul ℝ]
    abel
  rw [he] at hp
  exact sub_nonneg.mp hp

theorem threeProjectionLaplacian_polynomial (P R : Fin 3 → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hR : ∀ i, IsStarProjection (R i))
    (hPR : ∀ i, P i * R i = R i) (hQR : ∀ i, P (finRotate 3 i) * R i = R i)
    (c : ℝ) (hc : 0 ≤ c) (hangle : ∀ i, ‖P i * P (finRotate 3 i) - R i‖ ≤ c) :
    (1 - 2 * c) • projectionLaplacian P ≤ projectionLaplacian P * projectionLaplacian P := by
  have hp (i : Fin 3) := starProjection_pair_residual_polynomial
    (hP i) (hP (finRotate 3 i)) (hR i) (hPR i) (hQR i) c hc (hangle i)
  rw [projectionLaplacian, Fin.sum_univ_three]
  apply threeStarProjections_polynomial (hP 0).one_sub (hP 1).one_sub (hP 2).one_sub c
  · simpa only [finRotate_apply, show (0 : Fin 3) + 1 = 1 from rfl] using hp 0
  · simpa only [finRotate_apply, show (1 : Fin 3) + 1 = 2 from rfl] using hp 1
  · simpa only [finRotate_apply, show (2 : Fin 3) + 1 = 0 from rfl] using hp 2

theorem threeProjectionLaplacian_gap (P R : Fin 3 → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hR : ∀ i, IsStarProjection (R i))
    (hPR : ∀ i, P i * R i = R i) (hQR : ∀ i, P (finRotate 3 i) * R i = R i)
    (c : ℝ) (hc : 0 ≤ c) (hangle : ∀ i, ‖P i * P (finRotate 3 i) - R i‖ ≤ c)
    (x : H) (hx : x ∈ (⨅ i, (P i).eqLocus (1 : H →L[ℂ] H))ᗮ) :
    (1 - 2 * c) * ‖x‖ ^ 2 ≤ ∑ i, ‖x - P i x‖ ^ 2 := by
  rw [← projectionLaplacian_ker P hP] at hx
  rw [← projectionLaplacian_energy P hP]
  exact positive_polynomial_gap (projectionLaplacian P) (projectionLaplacian_nonneg P hP)
    (1 - 2 * c) (threeProjectionLaplacian_polynomial P R hP hR hPR hQR c hc hangle) x hx

end ThomGame.Analysis
