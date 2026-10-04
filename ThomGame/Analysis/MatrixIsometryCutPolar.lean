module

public import ThomGame.Analysis.MatrixThomSpectralCorrection
public import ThomGame.Analysis.MatrixPolarExactIntertwining

/-!
# Rank and distance of the actual polar correction of a cut isometry

The polar factor of QV remains supported by Q. Its rank loses at most
the deleted Hilbert--Schmidt mass, and its squared distance to V is at
most twice that mass. Exact common star intertwining is preserved.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixRectPolar_gram_le_initial (X : Matrix (Fin m) (Fin d) ℂ) (hX : Xᴴ * X ≤ 1) :
    Xᴴ * X ≤ (matrixRectPolar X)ᴴ * matrixRectPolar X := by
  let E := (matrixRectPolar X)ᴴ * matrixRectPolar X
  have hE : IsStarProjection E := matrixRectPolar_initial_projection X
  have hXE : X * E = X := by
    dsimp only [E]
    rw [matrixRectPolar_initial]
    exact matrix_mul_absSupport X
  have hEX : E * Xᴴ = Xᴴ := by
    simpa only [Matrix.conjTranspose_mul, hE.isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose hXE
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hX)).conjTranspose_mul_mul_same E
  have he : Eᴴ * (1 - Xᴴ * X) * E = E - Xᴴ * X := by
    rw [hE.isSelfAdjoint.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hE.isIdempotentElem.eq, ← Matrix.mul_assoc E Xᴴ X, hEX, Matrix.mul_assoc, hXE]
  rw [he] at hp
  exact sub_nonneg.mp hp.nonneg

theorem matrixCutIsometry_polar_support (V : Matrix (Fin m) (Fin d) ℂ)
    {Q : CMatrix m} (hQ : IsStarProjection Q) :
    Q * matrixRectPolar (Q * V) = matrixRectPolar (Q * V) := by
  rw [matrixRectPolar, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.isIdempotentElem.eq]

theorem matrixCutIsometry_gram_loss (r : Nat) (V : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) {Q : CMatrix m} (hQ : IsStarProjection Q) :
    rectHSNorm r ((1 - Q) * V) ^ 2 = matrixTraceReal r (1 : CMatrix d) -
      matrixTraceReal r ((Q * V)ᴴ * (Q * V)) := by
  rw [← matrixTraceReal_gram, matrixProjection_compression_gram hQ.one_sub,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, matrixTraceReal_sub,
    matrixProjection_compression_gram hQ]

theorem matrixCutIsometry_polar_distance_le (r : Nat) (V : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) {Q : CMatrix m} (hQ : IsStarProjection Q) :
    rectHSNorm r (matrixRectPolar (Q * V) - V) ^ 2 ≤ 2 * rectHSNorm r ((1 - Q) * V) ^ 2 := by
  let W := matrixRectPolar (Q * V)
  have hWQ : Wᴴ * Q = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose (matrixCutIsometry_polar_support V hQ)
  have hc : Wᴴ * V = matrixRectAbs (Q * V) := by
    rw [← hWQ, Matrix.mul_assoc]
    exact matrixRectPolar_adjoint_mul (Q * V)
  have hg : (Q * V)ᴴ * (Q * V) ≤ 1 := by
    simpa only [hV] using matrixProjection_compression_gram_le hQ V
  have ha := matrixTraceReal_mono r (matrixRectAbs_ge_gram_of_gram_le_one hg)
  have hi := matrixTraceReal_mono r (matrixRectPolar_initial_projection (Q * V)).le_one
  rw [rectHSNorm_sub_sq, hV, hc, matrixCutIsometry_gram_loss r V hV hQ]
  dsimp only [W] at *
  linarith

theorem matrixCutIsometry_polar_rank_bound (r : Nat) (V : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) {Q : CMatrix m} (hQ : IsStarProjection Q) :
    matrixTraceReal r (1 : CMatrix d) - rectHSNorm r ((1 - Q) * V) ^ 2 ≤
      ((matrixRectPolar (Q * V)).rank : ℝ) / r := by
  have hg : (Q * V)ᴴ * (Q * V) ≤ 1 := by
    simpa only [hV] using matrixProjection_compression_gram_le hQ V
  have he := matrixTraceReal_mono r (matrixRectPolar_gram_le_initial (Q * V) hg)
  rw [matrixTraceReal_projection_rank r (matrixRectPolar_initial_projection (Q * V)),
    Matrix.rank_conjTranspose_mul_self] at he
  rw [matrixCutIsometry_gram_loss r V hV hQ]
  linarith

variable [NeZero d]

theorem MatrixThomSpectralData.polar_correction {A B D : StarSubalgebra ℂ (CMatrix d)}
    {ε : ℝ} (S : MatrixThomSpectralData A B D ε) :
    ∃ W : Matrix (Fin (d * (d * d))) (Fin d) ℂ,
      W = matrixRectPolar (S.cut * S.isometry) ∧
      IsStarProjection (Wᴴ * W) ∧ IsStarProjection (W * Wᴴ) ∧ S.cut * W = W ∧
      rectHSNorm d (W - S.isometry) ^ 2 ≤ 4 * ε ^ 2 ∧
      1 - 2 * ε ^ 2 ≤ (W.rank : ℝ) / d ∧
      (∀ X ∈ D, S.sourceRep X * W = W * X) ∧
      ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)), S.commutantRep X * W = W * X := by
  let W := matrixRectPolar (S.cut * S.isometry)
  have hd := matrixCutIsometry_polar_distance_le d S.isometry S.isometry_gram S.cut_projection
  have hr := matrixCutIsometry_polar_rank_bound d S.isometry S.isometry_gram S.cut_projection
  have ht : matrixTraceReal d (1 : CMatrix d) = 1 := by simp [matrixTraceReal, NeZero.ne d]
  rw [ht] at hr
  refine ⟨W, rfl, matrixRectPolar_initial_projection _, matrixRectPolar_final_projection _,
    matrixCutIsometry_polar_support _ S.cut_projection, (by linarith [S.deleted_mass_le]),
    (by linarith [S.deleted_mass_le]), ?_, ?_⟩
  · intro X hX
    apply Eq.symm
    apply matrixRectPolar_exact_intertwining
    · exact (S.cut_common_intertwines X hX).symm
    · have he := S.cut_common_intertwines (star X) (D.star_mem' hX)
      rw [map_star] at he
      exact he.symm
  · intro X hX
    apply Eq.symm
    apply matrixRectPolar_exact_intertwining
    · exact (S.cut_commutant_intertwines X hX).symm
    · have he := S.cut_commutant_intertwines (star X)
        ((StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).star_mem' hX)
      rw [map_star] at he
      exact he.symm

end ThomGame.Analysis
