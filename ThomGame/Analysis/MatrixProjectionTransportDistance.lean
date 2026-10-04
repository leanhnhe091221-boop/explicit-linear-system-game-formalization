module

public import ThomGame.Analysis.MatrixProjectionPolarTransport

/-!
# Sharp projection distance under polar transport

The compressed polar factor controls the overlap of the two projections.
The projection-distance identity then gives the factor 2 in ALT (4.6),
without losing a factor through a triangle inequality for the polar map.
All rectangular traces retain the original ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_supported_square_lower {p A : Matrix ι ι ℂ}
    (hp : IsStarProjection p) (hpA : p * A = A) (hAp : A * p = A)
    {c : ℝ} (hc : 0 ≤ c) (hlower : c • p ≤ A) : c ^ 2 • p ≤ A * A := by
  let D := A - c • p
  have hD : 0 ≤ D := sub_nonneg.mpr hlower
  have hsq : 0 ≤ D * D := by
    simpa only [hD.isSelfAdjoint.star_eq] using star_mul_self_nonneg D
  have he := add_nonneg hsq (smul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hD)
  apply sub_nonneg.mp
  convert he using 1
  dsimp only [D]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    hpA, hAp, hp.isIdempotentElem.eq, smul_smul, smul_sub]
  module

theorem matrixPartialIsometry_transport_projection {W P p : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hp : IsStarProjection p) (hW : Wᴴ * W = P) (hpP : p ≤ P) :
    IsStarProjection (W * p * Wᴴ) := by
  have hPp := (hp.le_iff_mul_eq_right hP).mp hpP
  constructor
  · show (W * p * Wᴴ) * (W * p * Wᴴ) = W * p * Wᴴ
    calc
      _ = W * p * (Wᴴ * W) * p * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW, Matrix.mul_assoc (W * p), hPp,
        Matrix.mul_assoc W p p, hp.isIdempotentElem.eq]
  · show (W * p * Wᴴ)ᴴ = W * p * Wᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hp.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

theorem matrixProjection_conjugate_le_gram {p : Matrix ι ι ℂ}
    (hp : IsStarProjection p) (W : Matrix ι ι ℂ) :
    W * p * Wᴴ ≤ W * Wᴴ := by
  have hz : 0 ≤ (1 : Matrix ι ι ℂ) - p := hp.one_sub.nonneg
  have he := (Matrix.nonneg_iff_posSemidef.mp hz).mul_mul_conjTranspose_same W
  apply sub_nonneg.mp
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] using he.nonneg

theorem matrixTraceReal_partialIsometry_transport (r : Nat) {W P p : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hp : IsStarProjection p) (hW : Wᴴ * W = P) (hpP : p ≤ P) :
    matrixTraceReal r (W * p * Wᴴ) = matrixTraceReal r p := by
  rw [matrixTraceReal_mul_comm r (W * p) Wᴴ, ← Matrix.mul_assoc, hW,
    (hp.le_iff_mul_eq_right hP).mp hpP]

theorem matrixPartialIsometry_transport_rank {W P p : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hp : IsStarProjection p) (hW : Wᴴ * W = P) (hpP : p ≤ P) :
    (W * p * Wᴴ).rank = p.rank := by
  have he := matrixTraceReal_partialIsometry_transport 1 hP hp hW hpP
  rw [matrixTraceReal_projection_rank 1 (matrixPartialIsometry_transport_projection hP hp hW hpP),
    matrixTraceReal_projection_rank 1 hp, Nat.cast_one, div_one, div_one] at he
  exact_mod_cast he

theorem rectHSNorm_partialIsometry_transport_sq_le (r : Nat) {W P p : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hp : IsStarProjection p) (hW : Wᴴ * W = P) (hpP : p ≤ P)
    {c : ℝ} (hc : 0 ≤ c) (hcomp : c • p ≤ p * W * p) :
    rectHSNorm r (W * p * Wᴴ - p) ^ 2 ≤ 2 * (1 - c ^ 2) * matrixTraceReal r p := by
  let C := p * W * p
  let q := W * p * Wᴴ
  have hq : IsStarProjection q := matrixPartialIsometry_transport_projection hP hp hW hpP
  have hC : 0 ≤ C := (smul_nonneg hc hp.nonneg).trans hcomp
  have hpC : p * C = C := by
    dsimp only [C]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hp.isIdempotentElem.eq]
  have hCp : C * p = C := by
    dsimp only [C]
    rw [Matrix.mul_assoc, hp.isIdempotentElem.eq]
  have hs := matrixTraceReal_mono r (matrix_supported_square_lower hp hpC hCp hc hcomp)
  have hCC : C * C = p * q * p := by
    calc
      _ = C * Cᴴ := by rw [hC.isSelfAdjoint.isHermitian.eq]
      _ = _ := by
        dsimp only [C, q]
        simp only [Matrix.conjTranspose_mul, hp.isSelfAdjoint.isHermitian.eq]
        calc
          _ = p * W * (p * p) * Wᴴ * p := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hp.isIdempotentElem.eq]; simp only [Matrix.mul_assoc]
  have ht : matrixTraceReal r (C * C) = matrixTraceReal r (q * p) := by
    rw [hCC, Matrix.mul_assoc, matrixTraceReal_mul_comm r p (q * p),
      Matrix.mul_assoc, hp.isIdempotentElem.eq]
  rw [matrixTraceReal_real_smul, ht] at hs
  have htrace : matrixTraceReal r q = matrixTraceReal r p :=
    matrixTraceReal_partialIsometry_transport r hP hp hW hpP
  change rectHSNorm r (q - p) ^ 2 ≤ _
  rw [rectHSNorm_sub_sq_hermitian r hq.isSelfAdjoint.isHermitian hp.isSelfAdjoint.isHermitian,
    hq.isIdempotentElem.eq, hp.isIdempotentElem.eq, htrace]
  nlinarith only [hs]

theorem rectHSNorm_projectionPolar_transport_sq_le (r : Nat) {P R p : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hp : IsStarProjection p) (hpP : p ≤ P)
    {ε : ℝ} (hε : ε < 1) (hleak : P * (1 - R) * P ≤ ε • P) :
    rectHSNorm r (matrixRectPolar (R * P) * p * (matrixRectPolar (R * P))ᴴ - p) ^ 2 ≤
      2 * ε * matrixTraceReal r p := by
  have hPp := (hp.le_iff_mul_eq_right hP).mp hpP
  have hpP' := (hp.le_iff_mul_eq_left hP).mp hpP
  have hcomp : Real.sqrt (1 - ε) • p ≤ p * matrixRectPolar (R * P) * p := by
    have he := star_right_conjugate_le_conjugate (matrixProjectionPolar_abs_lower hP hR hε.le hleak) p
    simp only [hp.isSelfAdjoint.star_eq, Matrix.mul_smul, Matrix.smul_mul,
      hpP', hp.isIdempotentElem.eq] at he
    have hh : p * matrixRectAbs (R * P) * p = p * matrixRectPolar (R * P) * p := by
      rw [← matrixProjectionPolar_compression hP hR,
        ← Matrix.mul_assoc p (P * matrixRectPolar (R * P)), ← Matrix.mul_assoc p P,
        hpP', Matrix.mul_assoc (p * matrixRectPolar (R * P)), hPp]
    rwa [hh] at he
  have he := rectHSNorm_partialIsometry_transport_sq_le r hP hp
    (matrixProjectionPolar_initial hP hR hε hleak) hpP (Real.sqrt_nonneg _) hcomp
  simpa only [Real.sq_sqrt (sub_nonneg.mpr hε.le), sub_sub_cancel] using he

theorem matrixCoordinateEnergy_projectionPolar_transport_le {d h : Nat} [NeZero h]
    (U : Fin h → UnitaryMatrix d) {P R p : CMatrix d}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hp : IsStarProjection p) (hpP : p ≤ P)
    {ε : ℝ} (hε : ε < 1) (hleak : P * (1 - R) * P ≤ ε • P) :
    matrixCoordinateEnergy U (matrixRectPolar (R * P) * p * (matrixRectPolar (R * P))ᴴ) ≤
      2 * matrixCoordinateEnergy U p + 4 * ε * matrixTraceReal d p := by
  have he := matrixIntertwiningEnergy_perturb_le d U U
    (matrixRectPolar (R * P) * p * (matrixRectPolar (R * P))ᴴ) p
  have hd := rectHSNorm_projectionPolar_transport_sq_le d hP hR hp hpP hε hleak
  simp only [matrixIntertwiningEnergy_eq_coordinate] at he
  linarith

end ThomGame.Analysis
