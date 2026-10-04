module

public import ThomGame.Analysis.MatrixStinespringBlockEnergy
public import ThomGame.Analysis.MatrixStinespringCommutatorEnergy
public import ThomGame.Analysis.MatrixStinespringReindex

/-!
# Thom Lemma 4.1: the uniform reverse-inclusion estimate

The proof constructs a finite Stinespring dilation of the actual trace
expectation. Matrix-unit averaging computes its exact commutant variance;
the commutator estimate applies directly to every contraction.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixReverseInclusion_scale_sq (X : CMatrix d) (hXC : X ∈ C) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - matrixTraceProjection B X) ^ 2 ≤
      2 * matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹) := by
  obtain ⟨ρ, _, _, _, V, hV, hE, _, _⟩ := exists_matrixRelativeStinespring_fin B
  let p := V * Vᴴ
  let H := StarSubalgebra.centralizer ℂ ((ρ.comp C.subtype).range : Set (CMatrix (d * (d * d))))
  let h := matrixTraceProjection H p
  have hc : ρ X * h = h * ρ X :=
    (mem_matrixSubalgebraCommutant_iff (ρ.comp C.subtype).range h).mp
      (matrixTraceProjection_mem H p) (ρ X) ⟨⟨X, hXC⟩, rfl⟩
  have hn : matrixOpNorm (ρ X) ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le ρ X).trans hX
  have hb := rectHSNorm_commutator_contraction_le d (ρ X) p h hn hc
  have hs := (sq_le_sq₀ (rectHSNorm_nonneg d _) (mul_nonneg (by norm_num) (rectHSNorm_nonneg d _))).mpr hb
  change rectHSNorm d (ρ X * (V * Vᴴ) - (V * Vᴴ) * ρ X) ^ 2 ≤
    (2 * rectHSNorm d ((V * Vᴴ) - matrixTraceProjection H (V * Vᴴ))) ^ 2 at hs
  rw [matrixStinespring_expectation_commutator_sq B ρ V hV hE, mul_pow,
    matrixStinespring_commutant_variance_scale B C P Q hBC ρ V hV hE] at hs
  linarith

include hBC in
theorem matrixReverseInclusion_scale (X : CMatrix d) (hXC : X ∈ C) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - matrixTraceProjection B X) ≤
      Real.sqrt 2 * Real.sqrt (matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹)) := by
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (matrixInclusionScaleRatio_trace_defect_nonneg B C P Q hBC d)]
  exact matrixReverseInclusion_scale_sq B C P Q hBC X hXC hX

include hBC in
theorem matrixReverseInclusion_scale_error :
    matrixNearInclusionError C B ≤
      Real.sqrt 2 * Real.sqrt (matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹)) := by
  obtain ⟨X, hXC, hX, hmax⟩ := exists_matrixNearInclusion_maximizer C B
  rw [← hmax]
  exact matrixReverseInclusion_scale B C P Q hBC X hXC hX

include hBC in
theorem matrixThom_lemma_4_1 :
    1 ≤ matrixInclusionScaleRatio B C P Q ∧
      matrixNearInclusionError C B ≤
        Real.sqrt 2 * Real.sqrt (matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹)) :=
  ⟨matrixInclusionScaleRatio_one_le B C P Q hBC, matrixReverseInclusion_scale_error B C P Q hBC⟩

include hBC in
theorem matrixReverseInclusion_scale_near :
    MatrixNearInclusion C B
      (Real.sqrt 2 * Real.sqrt (matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹))) :=
  (matrixNearInclusion_iff_error_le C B _).mpr (matrixReverseInclusion_scale_error B C P Q hBC)

end ThomGame.Analysis
