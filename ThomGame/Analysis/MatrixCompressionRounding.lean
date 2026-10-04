module

public import ThomGame.Analysis.MatrixHalfSpectralCut
public import ThomGame.Analysis.MatrixProjectionTransportDistance
public import ThomGame.Analysis.MatrixProjectionRankTrace

/-!
# Half spectral rounding of a single compressed projection

For x = b y b the closed half cut stays beneath b and has rank at
most rank y. The support estimate yields the sharp factor two in
the distance and trace-loss bounds, in the original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem half_step_support_error (x : ℝ) :
    2 * x + spectralStep (1 / 2) x - 2 * (x * spectralStep (1 / 2) x) ≤
      if x = 0 then 0 else 1 := by
  by_cases hz : x = 0
  · subst x
    norm_num [spectralStep]
  · rw [ite_eq_right hz]
    by_cases hx : (1 / 2 : ℝ) ≤ x
    · simp only [spectralStep, ite_eq_left hx]
      linarith
    · simp only [spectralStep, ite_eq_right hx]
      linarith

variable {d : Nat}

theorem matrixHalfProjection_support_bound {A : CMatrix d} (hA : Matrix.IsHermitian A) :
    (2 : ℝ) • A + matrixHalfProjection A - (2 : ℝ) • (A * matrixHalfProjection A) ≤
      matrixRealSupport A := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  have he : cfc (fun x : ℝ => 2 * x + spectralStep (1 / 2) x -
      2 * (x * spectralStep (1 / 2) x)) A =
      (2 : ℝ) • A + matrixHalfProjection A - (2 : ℝ) • (A * matrixHalfProjection A) := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_add A _ _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _),
      cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _),
      cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hid]
    rfl
  rw [← he, matrixRealSupport]
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro x _
  exact half_step_support_error x

theorem matrixHalfProjection_le_support {A : CMatrix d} :
    matrixHalfProjection A ≤ matrixRealSupport A := by
  unfold matrixHalfProjection matrixRealSupport
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro x _
  by_cases hz : x = 0
  · subst x
    norm_num [spectralStep]
  · simp only [ite_eq_right hz]
    unfold spectralStep
    split_ifs <;> norm_num

theorem matrixRealSupport_le_projection {A b : CMatrix d} (hA : Matrix.IsHermitian A)
    (hb : IsStarProjection b) (hAb : A * b = A) : matrixRealSupport A ≤ b := by
  apply ((matrixRealSupport_isStarProjection A).le_iff_mul_eq_left hb).mpr
  rw [← matrixRealInv_mul hA, Matrix.mul_assoc, hAb]

theorem matrixProjection_compression_bounds {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    0 ≤ b * y * b ∧ b * y * b ≤ 1 := by
  have hlo := (Matrix.nonneg_iff_posSemidef.mp hy.nonneg).mul_mul_conjTranspose_same b
  have hup := matrixProjection_conjugate_le_gram hy b
  simp only [hb.isSelfAdjoint.isHermitian.eq, hb.isIdempotentElem.eq] at hlo hup
  exact ⟨hlo.nonneg, hup.trans hb.le_one⟩

theorem matrixHalfProjection_compression_le {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    matrixHalfProjection (b * y * b) ≤ b := by
  have hA := (matrixProjection_compression_bounds hb hy).1.isSelfAdjoint.isHermitian
  exact matrixHalfProjection_le_support.trans (matrixRealSupport_le_projection hA hb (by
    rw [Matrix.mul_assoc, hb.isIdempotentElem.eq]))

theorem matrixHalfProjection_compression_rank_le {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    (matrixHalfProjection (b * y * b)).rank ≤ y.rank := by
  have hA := (matrixProjection_compression_bounds hb hy).1.isSelfAdjoint.isHermitian
  exact (matrix_cfc_rank_le hA (spectralStep (1 / 2)) (by norm_num [spectralStep])).trans
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

theorem matrixHalfProjection_compression_pairing (r : Nat) {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    matrixTraceReal r (y * matrixHalfProjection (b * y * b)) =
      matrixTraceReal r ((b * y * b) * matrixHalfProjection (b * y * b)) := by
  let z := matrixHalfProjection (b * y * b)
  have hz := matrixHalfProjection_isStarProjection (b * y * b)
  have hzb := matrixHalfProjection_compression_le hb hy
  have hleft : b * z = z := (hz.le_iff_mul_eq_right hb).mp hzb
  have hright : z * b = z := (hz.le_iff_mul_eq_left hb).mp hzb
  change matrixTraceReal r (y * z) = matrixTraceReal r ((b * y * b) * z)
  rw [Matrix.mul_assoc (b * y), hleft, matrixTraceReal_mul_comm r (b * y) z,
    ← Matrix.mul_assoc, hright, matrixTraceReal_mul_comm r z y]

theorem matrixHalfProjection_compression_distance_le (r : Nat) {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    rectHSNorm r (y - matrixHalfProjection (b * y * b)) ^ 2 ≤
      2 * matrixTraceReal r ((1 - b) * y) := by
  let A := b * y * b
  let z := matrixHalfProjection A
  have hA := matrixProjection_compression_bounds hb hy
  have hz : IsStarProjection z := matrixHalfProjection_isStarProjection A
  have he := matrixTraceReal_mono r (matrixHalfProjection_support_bound hA.1.isSelfAdjoint.isHermitian)
  have hr : (matrixRealSupport A).rank ≤ y.rank :=
    (matrix_cfc_rank_le hA.1.isSelfAdjoint.isHermitian (fun x => if x = 0 then 0 else 1)
      (by norm_num)).trans
        ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
  have ht : matrixTraceReal r (matrixRealSupport A) ≤ matrixTraceReal r y := by
    rw [matrixTraceReal_projection_rank r (matrixRealSupport_isStarProjection A),
      matrixTraceReal_projection_rank r hy]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hr) (Nat.cast_nonneg r)
  have hpair : matrixTraceReal r (y * z) = matrixTraceReal r (A * z) :=
    matrixHalfProjection_compression_pairing r hb hy
  have htr : matrixTraceReal r A = matrixTraceReal r (b * y) := by
    rw [matrixTraceReal_mul_comm r (b * y) b, ← Matrix.mul_assoc, hb.isIdempotentElem.eq]
  change rectHSNorm r (y - z) ^ 2 ≤ _
  rw [rectHSNorm_sub_sq_hermitian r hy.isSelfAdjoint.isHermitian hz.isSelfAdjoint.isHermitian,
    hy.isIdempotentElem.eq, hz.isIdempotentElem.eq, hpair,
    Matrix.sub_mul, Matrix.one_mul, matrixTraceReal_sub]
  change matrixTraceReal r ((2 : ℝ) • A + z - (2 : ℝ) • (A * z)) ≤ _ at he
  simp only [matrixTraceReal_sub, matrixTraceReal_add, matrixTraceReal_real_smul] at he
  linarith only [he, ht, htr]

theorem matrixHalfProjection_compression_trace_ge (r : Nat) {b y : CMatrix d}
    (hb : IsStarProjection b) (hy : IsStarProjection y) :
    matrixTraceReal r y - 2 * matrixTraceReal r ((1 - b) * y) ≤
      matrixTraceReal r (matrixHalfProjection (b * y * b)) := by
  let z := matrixHalfProjection (b * y * b)
  have hz : IsStarProjection z := matrixHalfProjection_isStarProjection _
  have hd := matrixHalfProjection_compression_distance_le r hb hy
  have hp := matrixTraceReal_mono r (matrixProjection_conjugate_le_gram hy z)
  simp only [hz.isSelfAdjoint.isHermitian.eq, hz.isIdempotentElem.eq] at hp
  rw [matrixTraceReal_mul_comm r (z * y) z, ← Matrix.mul_assoc, hz.isIdempotentElem.eq,
    matrixTraceReal_mul_comm r z y] at hp
  change rectHSNorm r (y - z) ^ 2 ≤ _ at hd
  rw [rectHSNorm_sub_sq_hermitian r hy.isSelfAdjoint.isHermitian hz.isSelfAdjoint.isHermitian,
    hy.isIdempotentElem.eq, hz.isIdempotentElem.eq] at hd
  linarith only [hd, hp]

end ThomGame.Analysis
