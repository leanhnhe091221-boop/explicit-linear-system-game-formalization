module

public import ThomGame.Analysis.RectangularNormalizedTrace

/-!
# Mixing between two projections

The trace defect in ALT Lemma 3.4 is a squared off-diagonal HS norm.
Its bounds and its pairing with the range-projection tangent retain
the original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matrixTraceReal_projection_sandwich (r : Nat) {P : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (A : Matrix ι ι ℂ) :
    matrixTraceReal r (P * A * P) = matrixTraceReal r (P * A) := by
  rw [Matrix.mul_assoc, matrixTraceReal_mul_comm r P (A * P), Matrix.mul_assoc,
    hP.isIdempotentElem.eq, matrixTraceReal_mul_comm r A P]

omit [DecidableEq ι] in
theorem matrixTraceReal_projection_product_nonneg (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hP : IsStarProjection P) : 0 ≤ matrixTraceReal r (E * P) := by
  have he : matrixTraceReal r ((P * E)ᴴ * (P * E)) = matrixTraceReal r (E * P) := by
    rw [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq, hP.isSelfAdjoint.isHermitian.eq]
    calc
      _ = matrixTraceReal r (E * (P * P) * E) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP.isIdempotentElem.eq, matrixTraceReal_projection_sandwich r hE]
  rw [← he, matrixTraceReal_gram]
  exact sq_nonneg _

theorem matrixTraceReal_projection_product_le (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hP : IsStarProjection P) : matrixTraceReal r (E * P) ≤ matrixTraceReal r E := by
  have he := matrixTraceReal_projection_product_nonneg r hE hP.one_sub
  rw [Matrix.mul_sub, Matrix.mul_one, matrixTraceReal_sub] at he
  linarith

omit [DecidableEq ι] in
theorem matrixTraceReal_compression_square (r : Nat) {E : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (P : Matrix ι ι ℂ) :
    matrixTraceReal r ((E * P * E) * (E * P * E)) = matrixTraceReal r (E * P * E * P) := by
  calc
    _ = matrixTraceReal r (E * P * (E * E) * P * E) := by noncomm_ring
    _ = matrixTraceReal r (E * (P * E * P) * E) := by rw [hE.isIdempotentElem.eq]; noncomm_ring
    _ = _ := by rw [matrixTraceReal_projection_sandwich r hE]; simp only [Matrix.mul_assoc]

noncomputable def matrixProjectionMixing (r : Nat) (E P : Matrix ι ι ℂ) : ℝ :=
  matrixTraceReal r (E * P) - matrixTraceReal r (E * P * E * P)

theorem matrixProjectionMixing_eq_source (r : Nat) {E : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (P : Matrix ι ι ℂ) :
    matrixProjectionMixing r E P = matrixTraceReal r (E * P) - matrixTraceReal r ((E * P * E) ^ 2) := by
  rw [pow_two, matrixTraceReal_compression_square r hE]
  rfl

theorem matrixProjectionMixing_eq_hsNorm_sq (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hP : IsStarProjection P) :
    matrixProjectionMixing r E P = rectHSNorm r ((1 - P) * E * P) ^ 2 := by
  rw [← matrixTraceReal_gram]
  have halg : (((1 - P) * E * P)ᴴ * ((1 - P) * E * P)) = P * (E - E * P * E) * P := by
    simp only [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq,
      hP.isSelfAdjoint.isHermitian.eq, hP.one_sub.isSelfAdjoint.isHermitian.eq]
    calc
      _ = P * E * ((1 - P) * (1 - P)) * E * P := by noncomm_ring
      _ = P * (E * E - E * P * E) * P := by rw [hP.one_sub.isIdempotentElem.eq]; noncomm_ring
      _ = _ := by rw [hE.isIdempotentElem.eq]
  rw [halg, matrixTraceReal_projection_sandwich r hP, Matrix.mul_sub, matrixTraceReal_sub,
    matrixTraceReal_mul_comm r P E, matrixTraceReal_mul_comm r P (E * P * E)]
  simp only [matrixProjectionMixing, Matrix.mul_assoc]

theorem matrixProjectionMixing_nonneg (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hP : IsStarProjection P) : 0 ≤ matrixProjectionMixing r E P := by
  rw [matrixProjectionMixing_eq_hsNorm_sq r hE hP]
  exact sq_nonneg _

theorem matrixProjectionMixing_le_trace (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hP : IsStarProjection P) : matrixProjectionMixing r E P ≤ matrixTraceReal r E := by
  have hs : 0 ≤ matrixTraceReal r (E * P * E * P) := by
    rw [← matrixTraceReal_compression_square r hE P]
    have hh : (E * P * E)ᴴ = E * P * E := by
      simp only [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq,
        hP.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]
    have hgram := matrixTraceReal_gram r (E * P * E)
    rw [hh] at hgram
    rw [hgram]
    exact sq_nonneg _
  have he := matrixTraceReal_projection_product_le r hE hP
  unfold matrixProjectionMixing
  linarith

theorem matrixTraceReal_projection_tangent (r : Nat) {E P : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (t : ℝ) :
    matrixTraceReal r (E * (t • ((1 - P) * E * P + P * E * (1 - P)))) =
      2 * t * matrixProjectionMixing r E P := by
  have hleft : E * ((1 - P) * E * P) = E * P - E * P * E * P := by
    calc
      _ = E * E * P - E * P * E * P := by noncomm_ring
      _ = _ := by rw [hE.isIdempotentElem.eq]
  have hright : E * (P * E * (1 - P)) = E * P * E - E * P * E * P := by noncomm_ring
  rw [Matrix.mul_smul, matrixTraceReal_real_smul, Matrix.mul_add, hleft, hright,
    matrixTraceReal_add, matrixTraceReal_sub, matrixTraceReal_sub,
    matrixTraceReal_projection_sandwich r hE]
  unfold matrixProjectionMixing
  ring

omit [DecidableEq ι] in
theorem matrixProjectionMixing_continuous (r : Nat) (E : Matrix ι ι ℂ) :
    Continuous (matrixProjectionMixing r E) := by
  have ht : Continuous (matrixTraceReal (ι := ι) r) := (matrixTraceRealCLM r).continuous
  exact (ht.comp (continuous_const.mul continuous_id)).sub
    (ht.comp (((continuous_const.mul continuous_id).mul continuous_const).mul continuous_id))

end ThomGame.Analysis
