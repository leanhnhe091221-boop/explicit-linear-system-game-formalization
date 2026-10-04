module

public import ThomGame.Analysis.MatrixCommutantCornerEquivalence
public import ThomGame.Analysis.MatrixPartialIsometryCornerNorms

/-!
# Thom's actual support-corner identification

The original polar correction identifies p A p with q Ahat q by an
actual star algebra equivalence, preserving operator norms and every
originally normalized trace and HS norm. In particular it maps unit balls onto unit balls.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.cutPolar_initial_mem (S : MatrixThomSpectralData A B D ε) :
    S.cutPolarᴴ * S.cutPolar ∈ A :=
  matrixCommutantIntertwiner_initial_mem A S.cutCommutantRepresentation S.cutPolar S.cutPolar_commutant_intertwines

noncomputable def MatrixThomSpectralData.cutPolar_cornerEquiv (S : MatrixThomSpectralData A B D ε) :
    matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1 ≃⋆ₐ[ℂ]
      matrixSubalgebraCorner S.correctedTargetAlgebra (S.cutPolar * S.cutPolarᴴ) S.cutPolar_partialIsometry.2 :=
  matrixCommutantCornerEquiv A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_partialIsometry.1 S.cutPolar_commutant_intertwines

theorem MatrixThomSpectralData.cutPolar_cornerEquiv_apply (S : MatrixThomSpectralData A B D ε)
    (X : matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1) :
    (S.cutPolar_cornerEquiv X : CMatrix S.cut.rank) = S.cutPolar * (X : CMatrix d) * S.cutPolarᴴ := rfl

theorem MatrixThomSpectralData.cutPolar_corner_image (S : MatrixThomSpectralData A B D ε) :
    (fun X : CMatrix d => S.cutPolar * X * S.cutPolarᴴ) ''
      (matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1 : Set (CMatrix d)) =
      (matrixSubalgebraCorner S.correctedTargetAlgebra (S.cutPolar * S.cutPolarᴴ)
        S.cutPolar_partialIsometry.2 : Set (CMatrix S.cut.rank)) :=
  matrixCommutantCornerEquiv_image A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_partialIsometry.1 S.cutPolar_commutant_intertwines

theorem MatrixThomSpectralData.cutPolar_compressed_algebras (S : MatrixThomSpectralData A B D ε) :
    let W := S.cutPolar
    let p := Wᴴ * W
    let q := W * Wᴴ
    (fun X : CMatrix d => W * (p * X * p) * Wᴴ) '' (A : Set (CMatrix d)) =
      (fun Y : CMatrix S.cut.rank => q * Y * q) '' (S.correctedTargetAlgebra : Set (CMatrix S.cut.rank)) := by
  have he := S.cutPolar_corner_image
  rw [matrixSubalgebraCorner_eq_compressions A S.cutPolar_partialIsometry.1 S.cutPolar_initial_mem,
    matrixSubalgebraCorner_eq_compressions S.correctedTargetAlgebra S.cutPolar_partialIsometry.2
      S.cutPolar_final_mem_target, Set.image_image] at he
  exact he

theorem MatrixThomSpectralData.cutPolar_corner_norm (S : MatrixThomSpectralData A B D ε)
    (X : matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1) :
    matrixOpNorm (S.cutPolar_cornerEquiv X : CMatrix S.cut.rank) = matrixOpNorm (X : CMatrix d) :=
  matrixPartialIsometry_sandwich_norm_eq S.cutPolar S.cutPolar_partialIsometry.1 X X.property.2.1 X.property.2.2

theorem MatrixThomSpectralData.cutPolar_corner_trace (S : MatrixThomSpectralData A B D ε)
    (r : Nat) (X : matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1) :
    matrixTraceReal r (S.cutPolar_cornerEquiv X : CMatrix S.cut.rank) = matrixTraceReal r (X : CMatrix d) :=
  matrixSandwich_trace_of_support r S.cutPolar X X.property.2.1

theorem MatrixThomSpectralData.cutPolar_corner_hsNorm (S : MatrixThomSpectralData A B D ε)
    (r : Nat) (X : matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1) :
    rectHSNorm r (S.cutPolar_cornerEquiv X : CMatrix S.cut.rank) = rectHSNorm r (X : CMatrix d) :=
  matrixSandwich_hsNorm_of_support r S.cutPolar X X.property.2.1 X.property.2.2

theorem MatrixThomSpectralData.cutPolar_corner_unitBall_image (S : MatrixThomSpectralData A B D ε) :
    (fun X : CMatrix d => S.cutPolar * X * S.cutPolarᴴ) ''
      {X : CMatrix d | X ∈ matrixSubalgebraCorner A (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1 ∧
        matrixOpNorm X ≤ 1} =
      {Y : CMatrix S.cut.rank | Y ∈ matrixSubalgebraCorner S.correctedTargetAlgebra (S.cutPolar * S.cutPolarᴴ)
        S.cutPolar_partialIsometry.2 ∧ matrixOpNorm Y ≤ 1} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hn⟩, rfl⟩
    exact ⟨matrixCommutantIntertwiner_push_corner A S.cutCommutantRepresentation S.cutPolar
      S.cutPolar_partialIsometry.1 S.cutPolar_commutant_intertwines X hX.1,
      (matrixPartialIsometry_sandwich_norm_le S.cutPolar S.cutPolar_partialIsometry.1 X).trans hn⟩
  · rintro ⟨hY, hn⟩
    refine ⟨S.cutPolar_cornerEquiv.symm ⟨Y, hY⟩, ⟨?_, ?_⟩, ?_⟩
    · exact (S.cutPolar_cornerEquiv.symm ⟨Y, hY⟩).property
    · have he := S.cutPolar_corner_norm (S.cutPolar_cornerEquiv.symm ⟨Y, hY⟩)
      rw [S.cutPolar_cornerEquiv.apply_symm_apply] at he
      exact he.symm.trans_le hn
    · exact congrArg Subtype.val (S.cutPolar_cornerEquiv.apply_symm_apply ⟨Y, hY⟩)

end ThomGame.Analysis
