module

public import ThomGame.Analysis.MatrixFrameScalarExtension
public import ThomGame.Analysis.MatrixThomCornerIdentification

/-!
# Thom's actual algebras in one stably enlarged matrix space

Both embeddings use the same polar correction W. Added corners carry
scalars, and the corrected B algebra is still exactly contained in the
corrected A algebra. The enlarged dimension differs from d by at most
the already controlled final complementary rank.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

noncomputable def MatrixThomSpectralData.stableDim (S : MatrixThomSpectralData A B D ε) : Nat :=
  S.cut.rank + (1 - S.cutPolarᴴ * S.cutPolar).rank

noncomputable def MatrixThomSpectralData.stableUnitary (S : MatrixThomSpectralData A B D ε) :
    UnitaryMatrix S.stableDim := matrixStableCompletionUnitary S.cutPolar S.cutPolar_partialIsometry.1

noncomputable def MatrixThomSpectralData.stableSourceFrame (S : MatrixThomSpectralData A B D ε) :
    Matrix (Fin S.stableDim) (Fin d) ℂ := matrixStableSourceFrame S.cutPolar S.cutPolar_partialIsometry.1

noncomputable def MatrixThomSpectralData.stableTargetFrame (S : MatrixThomSpectralData A B D ε) :
    Matrix (Fin S.stableDim) (Fin S.cut.rank) ℂ := matrixStableTargetFrame S.cutPolar

noncomputable def MatrixThomSpectralData.stableSourceCoordinateFrame (S : MatrixThomSpectralData A B D ε) :
    Matrix (Fin S.stableDim) (Fin d) ℂ :=
  matrixStableSourceCoordinateFrame S.cutPolar S.cutPolar_partialIsometry.1

theorem MatrixThomSpectralData.stableSourceFrame_initial (S : MatrixThomSpectralData A B D ε) :
    S.stableSourceFrameᴴ * S.stableSourceFrame = 1 :=
  matrixStableSourceFrame_initial S.cutPolar S.cutPolar_partialIsometry.1

theorem MatrixThomSpectralData.stableTargetFrame_initial (S : MatrixThomSpectralData A B D ε) :
    S.stableTargetFrameᴴ * S.stableTargetFrame = 1 := matrixStableTargetFrame_initial S.cutPolar

theorem MatrixThomSpectralData.stableSourceFrame_eq_unitary (S : MatrixThomSpectralData A B D ε) :
    S.stableUnitary.val * S.stableSourceCoordinateFrame =
      S.stableSourceFrame := matrixStableSourceFrame_eq_unitary S.cutPolar S.cutPolar_partialIsometry.1

theorem MatrixThomSpectralData.stableFrames_overlap (S : MatrixThomSpectralData A B D ε) :
    S.stableTargetFrameᴴ * S.stableSourceFrame = S.cutPolar :=
  matrixStableFrames_overlap S.cutPolar S.cutPolar_partialIsometry.1

noncomputable def MatrixThomSpectralData.stableOriginalAlgebra (S : MatrixThomSpectralData A B D ε)
    (C : StarSubalgebra ℂ (CMatrix d)) : StarSubalgebra ℂ (CMatrix S.stableDim) :=
  matrixFrameScalarAlgebra C S.stableSourceFrame S.stableSourceFrame_initial

noncomputable def MatrixThomSpectralData.stableCorrectedAlgebra (S : MatrixThomSpectralData A B D ε)
    (C : StarSubalgebra ℂ (CMatrix S.cut.rank)) : StarSubalgebra ℂ (CMatrix S.stableDim) :=
  matrixFrameScalarAlgebra C S.stableTargetFrame S.stableTargetFrame_initial

theorem MatrixThomSpectralData.stableCorrected_inclusion (S : MatrixThomSpectralData A B D ε) :
    S.stableCorrectedAlgebra S.correctedSourceAlgebra ≤ S.stableCorrectedAlgebra S.correctedTargetAlgebra :=
  matrixFrameScalarAlgebra_mono _ _ S.stableTargetFrame S.stableTargetFrame_initial
    S.correctedSourceAlgebra_le_target

theorem MatrixThomSpectralData.stableDim_eq (S : MatrixThomSpectralData A B D ε) :
    S.stableDim = d + (1 - S.cutPolar * S.cutPolarᴴ).rank :=
  (matrixPartialIsometry_stable_dimension_eq S.cutPolar S.cutPolar_partialIsometry.1).symm

theorem MatrixThomSpectralData.le_stableDim (S : MatrixThomSpectralData A B D ε) : d ≤ S.stableDim := by
  rw [S.stableDim_eq]
  omega

theorem MatrixThomSpectralData.stableDim_error (S : MatrixThomSpectralData A B D ε) :
    |(S.stableDim : ℝ) - d| ≤ 4 * ε ^ 2 * d := by
  rw [S.stableDim_eq, Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
  exact S.cutPolar_final_complement_rank

theorem MatrixThomSpectralData.stable_added_dimension_bounds (S : MatrixThomSpectralData A B D ε) :
    ((S.stableDim - d : Nat) : ℝ) ≤ 4 * ε ^ 2 * d ∧
      ((S.stableDim - S.cut.rank : Nat) : ℝ) ≤ 2 * ε ^ 2 * d := by
  constructor
  · rw [S.stableDim_eq, Nat.add_sub_cancel_left]
    exact S.cutPolar_final_complement_rank
  · change ((S.cut.rank + (1 - S.cutPolarᴴ * S.cutPolar).rank - S.cut.rank : Nat) : ℝ) ≤ _
    rw [Nat.add_sub_cancel_left]
    exact S.cutPolar_initial_complement_rank

theorem MatrixThomSpectralData.stableDim_ratio_bound (S : MatrixThomSpectralData A B D ε) :
    |(S.stableDim : ℝ) / d - 1| ≤ 4 * ε ^ 2 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have he : (S.stableDim : ℝ) / d - 1 = ((S.stableDim : ℝ) - d) / d := by
    rw [sub_div, div_self (ne_of_gt hd)]
  rw [he, abs_div, abs_of_pos hd]
  exact (div_le_iff₀ hd).mpr S.stableDim_error

end ThomGame.Analysis
