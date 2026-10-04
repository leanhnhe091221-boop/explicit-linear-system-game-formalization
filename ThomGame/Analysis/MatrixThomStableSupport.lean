module

public import ThomGame.Analysis.MatrixThomStableAlgebras

/-!
# A shared asymptotically full corner of the two actual stable A algebras

Compression to the common support sends either algebra into the other.
Its missing trace is exactly the sum of the original two missing traces,
using the original denominator d.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

noncomputable def MatrixThomSpectralData.stableSupport (S : MatrixThomSpectralData A B D ε) :
    CMatrix S.stableDim := matrixFrameLift S.stableSourceFrame (S.cutPolarᴴ * S.cutPolar)

theorem MatrixThomSpectralData.stableSupport_target (S : MatrixThomSpectralData A B D ε) :
    S.stableSupport = matrixFrameLift S.stableTargetFrame (S.cutPolar * S.cutPolarᴴ) :=
  matrixStableFrames_common_support S.cutPolar S.cutPolar_partialIsometry.1

theorem MatrixThomSpectralData.stableSupport_projection (S : MatrixThomSpectralData A B D ε) :
    IsStarProjection S.stableSupport :=
  matrixFrameLift_projection S.stableSourceFrame S.stableSourceFrame_initial _ S.cutPolar_partialIsometry.1

theorem MatrixThomSpectralData.stableSupport_source_mem (S : MatrixThomSpectralData A B D ε) :
    S.stableSupport ∈ S.stableOriginalAlgebra A :=
  matrixFrameScalarAlgebra_lift_mem A S.stableSourceFrame S.stableSourceFrame_initial _ S.cutPolar_initial_mem

theorem MatrixThomSpectralData.stableSupport_target_mem (S : MatrixThomSpectralData A B D ε) :
    S.stableSupport ∈ S.stableCorrectedAlgebra S.correctedTargetAlgebra := by
  rw [S.stableSupport_target]
  exact matrixFrameScalarAlgebra_lift_mem _ S.stableTargetFrame S.stableTargetFrame_initial _
    S.cutPolar_final_mem_target

theorem MatrixThomSpectralData.stableSupport_complement_trace (S : MatrixThomSpectralData A B D ε) :
    matrixTraceReal d (1 - S.stableSupport) ≤ 6 * ε ^ 2 := by
  have he : matrixTraceReal d (1 - S.stableSupport) =
      matrixTraceReal d (1 - S.cutPolarᴴ * S.cutPolar) + matrixTraceReal d (1 - S.cutPolar * S.cutPolarᴴ) :=
    matrixStableCommonSupport_complement_trace d S.cutPolar S.cutPolar_partialIsometry.1
  rw [he]
  linarith [S.cutPolar_complement_trace_bounds.1, S.cutPolar_complement_trace_bounds.2]

theorem MatrixThomSpectralData.stableSupport_source_compression (S : MatrixThomSpectralData A B D ε)
    (Z : CMatrix S.stableDim) (hZ : Z ∈ S.stableOriginalAlgebra A) :
    S.stableSupport * Z * S.stableSupport ∈ S.stableCorrectedAlgebra S.correctedTargetAlgebra := by
  let X := S.stableSourceFrameᴴ * Z * S.stableSourceFrame
  have hXA : X ∈ A := matrixFrameScalarAlgebra_compression_mem A S.stableSourceFrame
    S.stableSourceFrame_initial Z hZ
  have he : S.stableSupport * Z * S.stableSupport =
      matrixFrameLift S.stableSourceFrame ((S.cutPolarᴴ * S.cutPolar) * X * (S.cutPolarᴴ * S.cutPolar)) := by
    simp only [stableSupport, matrixFrameLift, X, Matrix.mul_assoc]
  rw [he]
  have hc := matrixStableFrames_source_corner S.cutPolar S.cutPolar_partialIsometry.1 X
  change matrixFrameLift S.stableSourceFrame _ = matrixFrameLift S.stableTargetFrame _ at hc
  rw [hc]
  apply matrixFrameScalarAlgebra_lift_mem
  exact matrixCommutantIntertwiner_push_mem A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_commutant_intertwines X hXA

theorem MatrixThomSpectralData.stableSupport_target_compression (S : MatrixThomSpectralData A B D ε)
    (Z : CMatrix S.stableDim) (hZ : Z ∈ S.stableCorrectedAlgebra S.correctedTargetAlgebra) :
    S.stableSupport * Z * S.stableSupport ∈ S.stableOriginalAlgebra A := by
  let Y := S.stableTargetFrameᴴ * Z * S.stableTargetFrame
  have hYA : Y ∈ S.correctedTargetAlgebra := matrixFrameScalarAlgebra_compression_mem _ S.stableTargetFrame
    S.stableTargetFrame_initial Z hZ
  have he : S.stableSupport * Z * S.stableSupport =
      matrixFrameLift S.stableTargetFrame ((S.cutPolar * S.cutPolarᴴ) * Y * (S.cutPolar * S.cutPolarᴴ)) := by
    rw [S.stableSupport_target]
    simp only [matrixFrameLift, Y, Matrix.mul_assoc]
  rw [he]
  have hc := matrixStableFrames_target_corner S.cutPolar S.cutPolar_partialIsometry.1 Y
  change matrixFrameLift S.stableTargetFrame _ = matrixFrameLift S.stableSourceFrame _ at hc
  rw [hc]
  apply matrixFrameScalarAlgebra_lift_mem
  exact matrixCommutantIntertwiner_pull_mem A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_commutant_intertwines Y hYA

theorem MatrixThomSpectralData.stableSupport_corners_eq (S : MatrixThomSpectralData A B D ε) :
    matrixSubalgebraCorner (S.stableOriginalAlgebra A) S.stableSupport S.stableSupport_projection =
      matrixSubalgebraCorner (S.stableCorrectedAlgebra S.correctedTargetAlgebra)
        S.stableSupport S.stableSupport_projection := by
  apply le_antisymm
  · intro Z hZ
    refine ⟨?_, hZ.2⟩
    have he := matrixSubalgebraCorner_compression_eq _ S.stableSupport_projection Z hZ
    rw [← he]
    exact S.stableSupport_source_compression Z hZ.1
  · intro Z hZ
    refine ⟨?_, hZ.2⟩
    have he := matrixSubalgebraCorner_compression_eq _ S.stableSupport_projection Z hZ
    rw [← he]
    exact S.stableSupport_target_compression Z hZ.1

end ThomGame.Analysis
