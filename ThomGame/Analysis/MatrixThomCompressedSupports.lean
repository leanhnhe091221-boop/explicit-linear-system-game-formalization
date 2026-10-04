module

public import ThomGame.Analysis.MatrixThomCompressedPolar
public import ThomGame.Analysis.MatrixProjectionRankSums

/-!
# The actual support corners of Thom's compressed polar correction

Star intertwining gives exact support commutation. Initial and final
complementary ranks are bounded in the original dimension d.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixStarIntertwining_support_commutation (W : Matrix (Fin m) (Fin d) ℂ)
    (R : CMatrix m) (X : CMatrix d) (h : R * W = W * X) (hs : Rᴴ * W = W * Xᴴ) :
    (Wᴴ * W) * X = X * (Wᴴ * W) ∧ (W * Wᴴ) * R = R * (W * Wᴴ) := by
  have ha : Wᴴ * R = X * Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hs
  constructor
  · rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc]

variable [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.cutPolar_commutant_supports
    (S : MatrixThomSpectralData A B D ε) (X : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    (S.cutPolarᴴ * S.cutPolar) * (X : CMatrix d) = (X : CMatrix d) * (S.cutPolarᴴ * S.cutPolar) ∧
      (S.cutPolar * S.cutPolarᴴ) * S.cutCommutantRepresentation X =
        S.cutCommutantRepresentation X * (S.cutPolar * S.cutPolarᴴ) := by
  apply matrixStarIntertwining_support_commutation S.cutPolar _ _ (S.cutPolar_commutant_intertwines X)
  have hs := S.cutPolar_commutant_intertwines (star X)
  change S.cutCommutantRepresentation (star X) * S.cutPolar = S.cutPolar * star (X : CMatrix d) at hs
  rw [map_star] at hs
  exact hs

theorem MatrixThomSpectralData.cutPolar_final_mem_target
    (S : MatrixThomSpectralData A B D ε) : S.cutPolar * S.cutPolarᴴ ∈ S.correctedTargetAlgebra := by
  apply (mem_matrixSubalgebraCommutant_iff S.cutCommutantRepresentation.range _).mpr
  intro Y hY
  have hy : ∃ X, S.cutCommutantRepresentation X = Y := hY
  obtain ⟨X, rfl⟩ := hy
  exact (S.cutPolar_commutant_supports X).2.symm

theorem MatrixThomSpectralData.cutPolar_common_supports
    (S : MatrixThomSpectralData A B D ε) (hDB : D ≤ B) (X : D) :
    (S.cutPolarᴴ * S.cutPolar) * (X : CMatrix d) = (X : CMatrix d) * (S.cutPolarᴴ * S.cutPolar) ∧
      (S.cutPolar * S.cutPolarᴴ) * S.cutSourceRepresentation ⟨X, hDB X.property⟩ =
        S.cutSourceRepresentation ⟨X, hDB X.property⟩ * (S.cutPolar * S.cutPolarᴴ) := by
  apply matrixStarIntertwining_support_commutation S.cutPolar _ _ (S.cutPolar_common_intertwines hDB X)
  have hs := S.cutPolar_common_intertwines hDB (star X)
  change S.cutSourceRepresentation (star (⟨X, hDB X.property⟩ : B)) * S.cutPolar =
    S.cutPolar * star (X : CMatrix d) at hs
  rw [map_star] at hs
  exact hs

theorem MatrixThomSpectralData.cutPolar_initial_complement_rank
    (S : MatrixThomSpectralData A B D ε) :
    ((1 - S.cutPolarᴴ * S.cutPolar).rank : ℝ) ≤ 2 * ε ^ 2 * d := by
  have hr := matrixProjection_rank_one_sub_add S.cutPolar_partialIsometry.1
  rw [Matrix.rank_conjTranspose_mul_self, Fintype.card_fin] at hr
  have he : ((1 - S.cutPolarᴴ * S.cutPolar).rank : ℝ) + (S.cutPolar.rank : ℝ) = d := by
    exact_mod_cast hr
  linarith [S.cutPolar_rank_lower]

theorem MatrixThomSpectralData.cutPolar_final_complement_rank
    (S : MatrixThomSpectralData A B D ε) :
    ((1 - S.cutPolar * S.cutPolarᴴ).rank : ℝ) ≤ 4 * ε ^ 2 * d := by
  have hr := matrixProjection_rank_one_sub_add S.cutPolar_partialIsometry.2
  rw [Matrix.rank_self_mul_conjTranspose, Fintype.card_fin] at hr
  have he : ((1 - S.cutPolar * S.cutPolarᴴ).rank : ℝ) + (S.cutPolar.rank : ℝ) = S.cut.rank := by
    exact_mod_cast hr
  have hd := (abs_le.mp S.dimension_error_absolute).2
  linarith [S.cutPolar_rank_lower]

theorem MatrixThomSpectralData.cutPolar_complement_trace_bounds
    (S : MatrixThomSpectralData A B D ε) :
    matrixTraceReal d (1 - S.cutPolarᴴ * S.cutPolar) ≤ 2 * ε ^ 2 ∧
      matrixTraceReal d (1 - S.cutPolar * S.cutPolarᴴ) ≤ 4 * ε ^ 2 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  rw [matrixTraceReal_projection_rank d S.cutPolar_partialIsometry.1.one_sub,
    matrixTraceReal_projection_rank d S.cutPolar_partialIsometry.2.one_sub]
  exact ⟨(div_le_iff₀ hd).mpr S.cutPolar_initial_complement_rank,
    (div_le_iff₀ hd).mpr S.cutPolar_final_complement_rank⟩

end ThomGame.Analysis
