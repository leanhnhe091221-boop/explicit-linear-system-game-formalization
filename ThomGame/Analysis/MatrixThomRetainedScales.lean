module

public import ThomGame.Analysis.MatrixRetainedBoundedScaleChanges
public import ThomGame.Analysis.MatrixThomStarMultiplicity

/-!
# Labelled positive scales for the same actual Thom correction

All objects below use the supplied spectral correction, including its
two representations and the restriction to the original common algebra.
The range equalities identify the retained blocks with the actual
corrected source and target algebras.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

noncomputable def MatrixThomSpectralData.retainedSourceScale : CMatrix S.cut.rank :=
  matrixSubalgebraScale _ (matrixStarRepresentationRetainedBlocks B P S.cutSourceRepresentation)

noncomputable def MatrixThomSpectralData.retainedTargetScale : CMatrix S.cut.rank :=
  matrixSubalgebraScale _ (matrixStarRepresentationRetainedComplementaryBlocks _ R S.cutCommutantRepresentation)

noncomputable def MatrixThomSpectralData.rawSourceScale : CMatrix S.cut.rank :=
  S.cutSourceRepresentation (matrixStarBlockScalarElement B P
    (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity B P B.subtype i))

noncomputable def MatrixThomSpectralData.rawTargetScale : CMatrix S.cut.rank :=
  S.cutCommutantRepresentation (matrixStarBlockScalarElement _ R
    (fun i => (matrixStarRepresentationMultiplicity _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype i : ℝ) / R.size i))

theorem MatrixThomSpectralData.retainedSourceScale_formula :
    S.retainedSourceScale P = S.cutSourceRepresentation (matrixStarBlockScalarElement B P
      (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity B P S.cutSourceRepresentation i)) :=
  matrixStarRepresentationRetainedBlocks_scale B P S.cutSourceRepresentation

theorem MatrixThomSpectralData.retainedTargetScale_formula :
    S.retainedTargetScale R = S.cutCommutantRepresentation (matrixStarBlockScalarElement _ R
      (fun i => (matrixStarRepresentationMultiplicity _ R S.cutCommutantRepresentation i : ℝ) / R.size i)) :=
  matrixStarRepresentationRetainedComplementary_scale _ R S.cutCommutantRepresentation

theorem MatrixThomSpectralData.retainedSourceScale_mem : S.retainedSourceScale P ∈ S.correctedSourceAlgebra := by
  rw [S.retainedSourceScale_formula P]
  exact ⟨_, rfl⟩

theorem MatrixThomSpectralData.retainedTargetScale_mem : S.retainedTargetScale R ∈ S.correctedTargetAlgebra := by
  change S.retainedTargetScale R ∈ StarSubalgebra.centralizer ℂ
    (S.cutCommutantRepresentation.range : Set (CMatrix S.cut.rank))
  rw [matrixStarRepresentation_commutant_eq _ R]
  exact matrixSubalgebraScale_mem _ _

theorem MatrixThomSpectralData.retainedSourceScale_posDef : (S.retainedSourceScale P).PosDef :=
  matrixSubalgebraScale_posDef _ _

theorem MatrixThomSpectralData.retainedTargetScale_posDef : (S.retainedTargetScale R).PosDef :=
  matrixSubalgebraScale_posDef _ _

variable (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)

noncomputable def MatrixThomSpectralData.commonRepresentation : D →⋆ₐ[ℂ] CMatrix S.cut.rank :=
  S.cutSourceRepresentation.comp (StarSubalgebra.inclusion hDB)

noncomputable def MatrixThomSpectralData.commonPositiveScalar (s : Fin F.count → ℝ) : CMatrix S.cut.rank :=
  S.commonRepresentation hDB (matrixStarBlockScalarElement D F s)

theorem MatrixThomSpectralData.commonRetainedRange_le_source :
    (matrixStarRepresentationBlocks D F (S.commonRepresentation hDB)).range ≤
      (matrixStarRepresentationBlocks B P S.cutSourceRepresentation).range := by
  rw [← matrixStarRepresentation_range_eq_blocks, ← matrixStarRepresentation_range_eq_blocks]
  rintro _ ⟨X, rfl⟩
  exact ⟨StarSubalgebra.inclusion hDB X, rfl⟩

theorem MatrixThomSpectralData.commonRetainedRange_le_target :
    (matrixStarRepresentationBlocks D F (S.commonRepresentation hDB)).range ≤
      (matrixStarRepresentationComplementary _ R S.cutCommutantRepresentation).range := by
  rw [← matrixStarRepresentation_range_eq_blocks, ← matrixStarRepresentation_commutant_eq]
  rintro _ ⟨X, rfl⟩
  exact S.correctedSourceAlgebra_le_target ⟨StarSubalgebra.inclusion hDB X, rfl⟩

theorem MatrixThomSpectralData.commonPositiveScalar_retained (s : Fin F.count → ℝ) :
    S.commonPositiveScalar hDB F s =
      matrixStarBlockScalar _ (matrixStarRepresentationRetainedBlocks D F (S.commonRepresentation hDB))
        (fun i => s (matrixStarRepresentationRetainedLabel D F (S.commonRepresentation hDB) i)) :=
  (matrixStarRepresentationRetainedBlocks_scalar D F (S.commonRepresentation hDB) s).symm

theorem MatrixThomSpectralData.commonPositiveScalar_posDef (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i) :
    (S.commonPositiveScalar hDB F s).PosDef := by
  rw [S.commonPositiveScalar_retained hDB F s]
  exact matrixStarBlockScalar_posDef _ _ (fun i => hs _)

end ThomGame.Analysis
