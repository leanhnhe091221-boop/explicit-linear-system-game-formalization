module

public import ThomGame.Analysis.MatrixThomStableBHausdorff

/-!
# Near inclusions with the stable ambient normalization

The original-denominator estimates imply the estimates normalized by
the enlarged dimension because N is at least d. No normalization is
silently identified with another one.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

open scoped Matrix.Norms.Frobenius in
theorem rectHSNorm_antitone_denominator {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r s : Nat} (hr : 0 < r) (hrs : r ≤ s) (X : Matrix ι κ ℂ) :
    rectHSNorm s X ≤ rectHSNorm r X := by
  unfold rectHSNorm
  exact div_le_div_of_nonneg_left (norm_nonneg X)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)) (Real.sqrt_le_sqrt (Nat.cast_le.mpr hrs))

theorem hsNorm_le_rectHSNorm_of_dimension_le {r n : Nat} (hr : 0 < r) (hrn : r ≤ n)
    (X : CMatrix n) : hsNorm X ≤ rectHSNorm r X := by
  rw [← rectHSNorm_eq_hsNorm]
  exact rectHSNorm_antitone_denominator hr hrn X

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stableSupport_compression_loss
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (Z : CMatrix S.stableDim) (hZ : matrixOpNorm Z ≤ 1) :
    rectHSNorm d (Z - S.stableSupport * Z * S.stableSupport) ≤ 2 * Real.sqrt 3 * ε := by
  have he := rectHSNorm_projection_compression_loss_sq d S.stableSupport Z S.stableSupport_projection hZ
  have ht := S.stableSupport_complement_trace
  have hp : 0 ≤ 2 * Real.sqrt 3 * ε := mul_nonneg (by positivity) hε
  have hs : (2 * Real.sqrt 3 * ε) ^ 2 = 12 * ε ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  nlinarith [rectHSNorm_nonneg d (Z - S.stableSupport * Z * S.stableSupport)]

theorem MatrixThomSpectralData.stable_A_nearInclusions
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) :
    MatrixNearInclusion (S.stableOriginalAlgebra A)
        (S.stableCorrectedAlgebra S.correctedTargetAlgebra) (2 * Real.sqrt 3 * ε) ∧
      MatrixNearInclusion (S.stableCorrectedAlgebra S.correctedTargetAlgebra)
        (S.stableOriginalAlgebra A) (2 * Real.sqrt 3 * ε) := by
  constructor
  · intro Z hZ hn
    exact ⟨S.stableSupport * Z * S.stableSupport, S.stableSupport_source_compression Z hZ,
      (hsNorm_le_rectHSNorm_of_dimension_le (NeZero.pos d) S.le_stableDim _).trans
        (S.stableSupport_compression_loss hε Z hn)⟩
  · intro Z hZ hn
    exact ⟨S.stableSupport * Z * S.stableSupport, S.stableSupport_target_compression Z hZ,
      (hsNorm_le_rectHSNorm_of_dimension_le (NeZero.pos d) S.le_stableDim _).trans
        (S.stableSupport_compression_loss hε Z hn)⟩

theorem MatrixThomSpectralData.stable_B_nearInclusions
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    MatrixNearInclusion (S.stableOriginalAlgebra B)
        (S.stableCorrectedAlgebra S.correctedSourceAlgebra) ((6 + 5 * Real.sqrt 2) * ε) ∧
      MatrixNearInclusion (S.stableCorrectedAlgebra S.correctedSourceAlgebra)
        (S.stableOriginalAlgebra B) ((6 + 5 * Real.sqrt 2) * ε) := by
  constructor
  · intro Z hZ hn
    obtain ⟨Y, hY, _, he⟩ := S.stable_B_forward_contraction hε hBA Z hZ hn
    exact ⟨Y, hY, (hsNorm_le_rectHSNorm_of_dimension_le (NeZero.pos d) S.le_stableDim _).trans he⟩
  · intro Z hZ hn
    obtain ⟨X, hX, _, he⟩ := S.stable_B_reverse_contraction hε hBA Z hZ hn
    exact ⟨X, hX, (hsNorm_le_rectHSNorm_of_dimension_le (NeZero.pos d) S.le_stableDim _).trans he⟩

end ThomGame.Analysis
