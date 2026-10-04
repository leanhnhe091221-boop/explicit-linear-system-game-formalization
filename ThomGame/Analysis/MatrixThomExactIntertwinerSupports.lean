module

public import ThomGame.Analysis.MatrixThomExactIntertwiner

/-!
# Asymptotically full exact B-intertwining supports

The polar part of the constructed average gives actual equivalent
subrepresentations. The missing dimensions are bounded by 8 and 10
times epsilon squared times the original dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat} {B : StarSubalgebra ℂ (CMatrix d)}

theorem matrixRepresentationIntertwiner_polar (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (T : Matrix (Fin m) (Fin d) ℂ) (hT : ∀ b : B, ρ b * T = T * (b : CMatrix d)) :
    ∀ b : B, ρ b * matrixRectPolar T = matrixRectPolar T * (b : CMatrix d) := by
  intro b
  apply Eq.symm
  apply matrixRectPolar_exact_intertwining
  · exact (hT b).symm
  · have hs := hT (star b)
    change ρ (star b) * T = T * star (b : CMatrix d) at hs
    rw [map_star] at hs
    exact hs.symm

theorem matrixRepresentationIntertwiner_gram_commutants (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (T : Matrix (Fin m) (Fin d) ℂ) (hT : ∀ b : B, ρ b * T = T * (b : CMatrix d)) :
    Tᴴ * T ∈ StarSubalgebra.centralizer ℂ (B : Set (CMatrix d)) ∧
      T * Tᴴ ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) := by
  have hc (b : B) : (Tᴴ * T) * (b : CMatrix d) = (b : CMatrix d) * (Tᴴ * T) ∧
      (T * Tᴴ) * ρ b = ρ b * (T * Tᴴ) := by
    apply matrixStarIntertwining_support_commutation T (ρ b) b (hT b)
    have hs := hT (star b)
    change ρ (star b) * T = T * star (b : CMatrix d) at hs
    rw [map_star] at hs
    exact hs
  constructor
  · apply (mem_matrixSubalgebraCommutant_iff B _).mpr
    intro b hb
    exact (hc ⟨b, hb⟩).1.symm
  · apply (mem_matrixSubalgebraCommutant_iff ρ.range _).mpr
    intro Y hY
    have hy : ∃ b, ρ b = Y := hY
    obtain ⟨b, rfl⟩ := hy
    exact (hc b).2.symm

variable [NeZero d] {A D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

noncomputable def MatrixThomSpectralData.exactIntertwiner
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    Matrix (Fin S.cut.rank) (Fin d) ℂ := Classical.choose (S.exists_exact_intertwiner hε hBA)

theorem MatrixThomSpectralData.exactIntertwiner_spec
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    (∀ b : B, S.cutSourceRepresentation b * S.exactIntertwiner hε hBA =
      S.exactIntertwiner hε hBA * (b : CMatrix d)) ∧
    rectHSNorm d (S.cutFrame * S.exactIntertwiner hε hBA - S.isometry) ≤ 2 * Real.sqrt 2 * ε ∧
    (d : ℝ) - 8 * ε ^ 2 * d ≤ (S.exactIntertwiner hε hBA).rank :=
  Classical.choose_spec (S.exists_exact_intertwiner hε hBA)

noncomputable def MatrixThomSpectralData.exactPolarIntertwiner
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    Matrix (Fin S.cut.rank) (Fin d) ℂ := matrixRectPolar (S.exactIntertwiner hε hBA)

theorem MatrixThomSpectralData.exactPolarIntertwiner_intertwines
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) (b : B) :
    S.cutSourceRepresentation b * S.exactPolarIntertwiner hε hBA =
      S.exactPolarIntertwiner hε hBA * (b : CMatrix d) :=
  matrixRepresentationIntertwiner_polar S.cutSourceRepresentation _ (S.exactIntertwiner_spec hε hBA).1 b

theorem MatrixThomSpectralData.exactPolarIntertwiner_supports
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    let U := S.exactPolarIntertwiner hε hBA
    IsStarProjection (Uᴴ * U) ∧ IsStarProjection (U * Uᴴ) ∧
      Uᴴ * U ∈ StarSubalgebra.centralizer ℂ (B : Set (CMatrix d)) ∧
      U * Uᴴ ∈ StarSubalgebra.centralizer ℂ (S.correctedSourceAlgebra : Set (CMatrix S.cut.rank)) := by
  dsimp only
  exact ⟨matrixRectPolar_initial_projection _, matrixRectPolar_final_projection _,
    matrixRepresentationIntertwiner_gram_commutants S.cutSourceRepresentation _
      (S.exactPolarIntertwiner_intertwines hε hBA)⟩

theorem MatrixThomSpectralData.exactPolarIntertwiner_rank_lower
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    (d : ℝ) - 8 * ε ^ 2 * d ≤ (S.exactPolarIntertwiner hε hBA).rank := by
  rw [MatrixThomSpectralData.exactPolarIntertwiner, matrixRectPolar_rank]
  exact (S.exactIntertwiner_spec hε hBA).2.2

theorem MatrixThomSpectralData.exactPolarIntertwiner_complement_ranks
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    let U := S.exactPolarIntertwiner hε hBA
    ((1 - Uᴴ * U).rank : ℝ) ≤ 8 * ε ^ 2 * d ∧
      ((1 - U * Uᴴ).rank : ℝ) ≤ 10 * ε ^ 2 * d := by
  let U := S.exactPolarIntertwiner hε hBA
  have hs := S.exactPolarIntertwiner_supports hε hBA
  have hi := matrixProjection_rank_one_sub_add hs.1
  have hf := matrixProjection_rank_one_sub_add hs.2.1
  rw [Fintype.card_fin] at hi hf
  change (1 - Uᴴ * U).rank + (Uᴴ * U).rank = d at hi
  change (1 - U * Uᴴ).rank + (U * Uᴴ).rank = S.cut.rank at hf
  rw [Matrix.rank_conjTranspose_mul_self] at hi
  rw [Matrix.rank_self_mul_conjTranspose] at hf
  have hi' : ((1 - Uᴴ * U).rank : ℝ) + (U.rank : ℝ) = d := by exact_mod_cast hi
  have hf' : ((1 - U * Uᴴ).rank : ℝ) + (U.rank : ℝ) = S.cut.rank := by exact_mod_cast hf
  have hr := S.exactPolarIntertwiner_rank_lower hε hBA
  have hd := (abs_le.mp S.dimension_error_absolute).2
  change ((1 - Uᴴ * U).rank : ℝ) ≤ _ ∧ ((1 - U * Uᴴ).rank : ℝ) ≤ _
  change (d : ℝ) - 8 * ε ^ 2 * d ≤ U.rank at hr
  constructor <;> linarith

theorem MatrixThomSpectralData.exactPolarIntertwiner_complement_traces
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    let U := S.exactPolarIntertwiner hε hBA
    matrixTraceReal d (1 - Uᴴ * U) ≤ 8 * ε ^ 2 ∧
      matrixTraceReal d (1 - U * Uᴴ) ≤ 10 * ε ^ 2 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hs := S.exactPolarIntertwiner_supports hε hBA
  have hr := S.exactPolarIntertwiner_complement_ranks hε hBA
  dsimp only
  rw [matrixTraceReal_projection_rank d hs.1.one_sub, matrixTraceReal_projection_rank d hs.2.1.one_sub]
  exact ⟨(div_le_iff₀ hd).mpr hr.1, (div_le_iff₀ hd).mpr hr.2⟩

theorem MatrixThomSpectralData.exactIntertwiner_rank_ratio_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    |((S.exactIntertwiner hε hBA).rank : ℝ) / d - 1| ≤ 8 * ε ^ 2 := by
  have hs := S.exactPolarIntertwiner_supports hε hBA
  have hb := (S.exactPolarIntertwiner_complement_traces hε hBA).1
  have hn := matrixTraceReal_nonneg d hs.1.one_sub.nonneg
  have ht : matrixTraceReal d (1 : CMatrix d) = 1 := by simp [matrixTraceReal, NeZero.ne d]
  have he : matrixTraceReal d
      (1 - (S.exactPolarIntertwiner hε hBA)ᴴ * S.exactPolarIntertwiner hε hBA) =
        1 - ((S.exactIntertwiner hε hBA).rank : ℝ) / d := by
    rw [matrixTraceReal_sub, ht, matrixTraceReal_projection_rank d hs.1,
      Matrix.rank_conjTranspose_mul_self, MatrixThomSpectralData.exactPolarIntertwiner, matrixRectPolar_rank]
  rw [he] at hb hn
  rw [abs_of_nonpos (by linarith)]
  linarith

end ThomGame.Analysis
