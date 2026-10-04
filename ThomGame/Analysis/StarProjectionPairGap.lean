module

public import ThomGame.Analysis.StarProjectionAngleNorm

/-! A root-pair angle controls the quadratic polynomial of its residual sum. -/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem starProjection_pair_residual_lower {P Q R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (hPR : P * R = R) (hQR : Q * R = R)
    (c : ℝ) (hc : 0 ≤ c) (hangle : ‖P * Q - R‖ ≤ c) :
    (1 - c) • (1 - R) ≤ (1 - P) + (1 - Q) := by
  have hRP : R * P = R := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using congrArg star hPR
  have hRQ : R * Q = R := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using congrArg star hQR
  let E := 1 - R
  let S := (P - R) + (Q - R)
  have hE : IsStarProjection E := hR.one_sub
  have hA := hR.sub_of_mul_eq_right hP hPR
  have hB := hR.sub_of_mul_eq_right hQ hQR
  have hAB : (P - R) * (Q - R) = P * Q - R := by
    rw [sub_mul, mul_sub, mul_sub, hPR, hRQ, hR.isIdempotentElem.eq]
    abel
  have hnorm : ‖S‖ ≤ 1 + c := starProjection_add_norm_le hA hB c hc (hAB ▸ hangle)
  have hpos : 0 ≤ S := add_nonneg hA.nonneg hB.nonneg
  have hle := (CStarAlgebra.norm_le_iff_le_algebraMap S (by linarith : 0 ≤ 1 + c) hpos).mp hnorm
  have hES : E * S = S := by
    dsimp only [E, S]
    simp only [sub_mul, mul_add, mul_sub, one_mul, hRP, hRQ, hR.isIdempotentElem.eq]
    abel
  have hSE : S * E = S := by
    dsimp only [E, S]
    simp only [add_mul, sub_mul, mul_sub, mul_one, hPR, hQR, hR.isIdempotentElem.eq]
    abel
  have hp := star_left_conjugate_nonneg (sub_nonneg.mpr hle) E
  have hinner : E * ((1 + c) • (1 : H →L[ℂ] H) - S) = (1 + c) • E - S := by
    rw [mul_sub, mul_smul_comm, mul_one, hES]
  rw [hE.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one, hinner,
    sub_mul, smul_mul_assoc, hE.isIdempotentElem.eq, hSE] at hp
  have hS : S ≤ (1 + c) • E := sub_nonneg.mp hp
  have hD : (1 - P) + (1 - Q) = (2 : ℝ) • E - S := by
    dsimp only [E, S]
    rw [two_smul ℝ]
    abel
  rw [hD]
  apply le_sub_iff_add_le.mpr
  have hsum := add_le_add_left hS ((1 - c) • E)
  rw [← add_smul, show (1 + c) + (1 - c) = (2 : ℝ) by ring] at hsum
  simpa only [add_comm] using hsum

theorem starProjection_pair_residual_polynomial {P Q R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (hPR : P * R = R) (hQR : Q * R = R)
    (c : ℝ) (hc : 0 ≤ c) (hangle : ‖P * Q - R‖ ≤ c) :
    (1 - c) • ((1 - P) + (1 - Q)) ≤ ((1 - P) + (1 - Q)) * ((1 - P) + (1 - Q)) := by
  let D := (1 - P) + (1 - Q)
  let E := 1 - R
  have hRP : R * P = R := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using congrArg star hPR
  have hRQ : R * Q = R := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using congrArg star hQR
  have hDE : D * E = D := by
    dsimp only [D, E]
    simp only [add_mul, sub_mul, mul_sub, mul_one, one_mul, hPR, hQR]
    abel
  have hED : E * D = D := by
    dsimp only [D, E]
    simp only [sub_mul, mul_add, mul_sub, one_mul, mul_one, hRP, hRQ]
    abel
  have hD : 0 ≤ D := add_nonneg hP.one_sub.nonneg hQ.one_sub.nonneg
  have hlower : (1 - c) • E ≤ D := starProjection_pair_residual_lower hP hQ hR hPR hQR c hc hangle
  have hcomm : Commute D (D - (1 - c) • E) := by
    change D * (D - (1 - c) • E) = (D - (1 - c) • E) * D
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hDE, hED]
  have hp := Commute.mul_nonneg hD (sub_nonneg.mpr hlower) hcomm
  rw [mul_sub, mul_smul_comm, hDE] at hp
  exact sub_nonneg.mp hp

end ThomGame.Analysis
