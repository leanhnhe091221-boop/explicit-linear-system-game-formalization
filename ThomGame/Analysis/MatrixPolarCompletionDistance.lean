module

public import ThomGame.Analysis.MatrixPolarCompletion

/-!
# Distance control for an actual completed compression polar factor

For a partial isometry Y and a projection E of the same rank as YY*,
completing the polar factor of EY produces Z with initial Y*Y, final
E, and squared HS distance at most that of the two range projections.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixTraceReal_conjTranspose (r : Nat) (A : Matrix ι ι ℂ) :
    matrixTraceReal r Aᴴ = matrixTraceReal r A := by
  simp [matrixTraceReal, Matrix.trace_conjTranspose]

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_sub_sq (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (X - Y) ^ 2 = matrixTraceReal r (Xᴴ * X) + matrixTraceReal r (Yᴴ * Y) -
      2 * matrixTraceReal r (Xᴴ * Y) := by
  have hcross : matrixTraceReal r (Yᴴ * X) = matrixTraceReal r (Xᴴ * Y) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      matrixTraceReal_conjTranspose r (Xᴴ * Y)
  have he := matrixTraceReal_gram r (X - Y)
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, matrixTraceReal_sub, hcross] at he
  linarith

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixProjection_compression_gram {E : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (Y : Matrix ι κ ℂ) :
    (E * Y)ᴴ * (E * Y) = Yᴴ * E * Y := by
  rw [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq]
  calc
    _ = Yᴴ * (E * E) * Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hE.isIdempotentElem.eq]

omit [DecidableEq κ] in
theorem matrixProjection_compression_gram_le {E : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (Y : Matrix ι κ ℂ) :
    (E * Y)ᴴ * (E * Y) ≤ Yᴴ * Y := by
  have he := (Matrix.nonneg_iff_posSemidef.mp hE.one_sub.nonneg).conjTranspose_mul_mul_same Y
  rw [matrixProjection_compression_gram hE]
  apply sub_nonneg.mp
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] using he.nonneg

omit [DecidableEq ι] in
theorem matrixRectAbs_ge_gram_of_gram_le_one {X : Matrix ι κ ℂ} (hX : Xᴴ * X ≤ 1) :
    Xᴴ * X ≤ matrixRectAbs X := by
  have hA := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have hid : cfc (fun x : ℝ => x) (Xᴴ * X) = Xᴴ * X := cfc_id' ℝ _ hA.isSelfAdjoint
  rw [matrixRectAbs, matrixSqrt_eq_real_cfc hA]
  conv_lhs => rw [← hid]
  apply cfc_mono _ ((Xᴴ * X).finite_real_spectrum.continuousOn _) ((Xᴴ * X).finite_real_spectrum.continuousOn _)
  intro x hx
  exact Real.le_sqrt_self_iff.mpr ((CFC.le_one_iff (R := ℝ) _ hA.isSelfAdjoint).mp hX x hx)

theorem exists_matrixPartialIsometry_close_to_projection (r : Nat)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y))
    {E : Matrix ι ι ℂ} (hE : IsStarProjection E) (hrank : E.rank = (Y * Yᴴ).rank) :
    ∃ Z : Matrix ι κ ℂ, Zᴴ * Z = Yᴴ * Y ∧ Z * Zᴴ = E ∧
      rectHSNorm r (Z - Y) ^ 2 ≤ rectHSNorm r (Y * Yᴴ - E) ^ 2 := by
  have hP := matrixPartialIsometry_final_projection hY
  have hr : (Yᴴ * Y).rank = E.rank := by
    rw [hrank, Matrix.rank_conjTranspose_mul_self, Matrix.rank_self_mul_conjTranspose]
  obtain ⟨Z, hZi, hZf, hZX⟩ := exists_matrixPolar_completion hY hE hr
    (X := E * Y) (by rw [Matrix.mul_assoc, matrixPartialIsometry_mul_initial hY])
    (by rw [← Matrix.mul_assoc, hE.isIdempotentElem.eq])
  have hZ : IsStarProjection (Zᴴ * Z) := hZi.symm ▸ hY
  have hEZ : E * Z = Z := by
    rw [← hZf, Matrix.mul_assoc]
    exact matrixPartialIsometry_mul_initial hZ
  have hZE : Zᴴ * E = Zᴴ := by
    simpa only [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq] using congrArg Matrix.conjTranspose hEZ
  have hZY : Zᴴ * Y = matrixRectAbs (E * Y) := by
    rw [← hZE, Matrix.mul_assoc]
    exact hZX
  have habs := matrixTraceReal_mono r (matrixRectAbs_ge_gram_of_gram_le_one
    ((matrixProjection_compression_gram_le hE Y).trans hY.le_one))
  have hgram : matrixTraceReal r ((E * Y)ᴴ * (E * Y)) = matrixTraceReal r (Y * Yᴴ * E) := by
    rw [matrixProjection_compression_gram hE, matrixTraceReal_mul_comm r (Yᴴ * E) Y]
    simp only [Matrix.mul_assoc]
  have htrace : matrixTraceReal r E = matrixTraceReal r (Yᴴ * Y) := by
    calc
      _ = matrixTraceReal r (Y * Yᴴ) := by
        rw [matrixTraceReal_projection_rank r hE, matrixTraceReal_projection_rank r hP, hrank]
      _ = _ := matrixTraceReal_mul_comm r Y Yᴴ
  refine ⟨Z, hZi, hZf, ?_⟩
  rw [rectHSNorm_sub_sq, hZi, hZY,
    rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian hE.isSelfAdjoint.isHermitian,
    hP.isIdempotentElem.eq, hE.isIdempotentElem.eq, htrace, matrixTraceReal_mul_comm r Y Yᴴ]
  rw [hgram] at habs
  linarith

end ThomGame.Analysis
