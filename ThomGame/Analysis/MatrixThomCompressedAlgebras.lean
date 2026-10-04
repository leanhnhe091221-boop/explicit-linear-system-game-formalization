module

public import ThomGame.Analysis.MatrixThomSpectralCorrection
public import ThomGame.Analysis.MatrixProjectionFinFrame
public import ThomGame.Analysis.MatrixReducingCompression

/-!
# Actual corrected algebras on Thom's spectral range

Both representations act on exactly rank Q coordinates. Their ranges
give the corrected source and the commutant defining the corrected target.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

noncomputable def MatrixThomSpectralData.cutFrame (S : MatrixThomSpectralData A B D ε) :
    Matrix (Fin (d * (d * d))) (Fin S.cut.rank) ℂ := matrixProjectionFinFrame S.cut_projection

theorem MatrixThomSpectralData.cutFrame_initial (S : MatrixThomSpectralData A B D ε) :
    S.cutFrameᴴ * S.cutFrame = 1 := matrixProjectionFinFrame_initial S.cut_projection

theorem MatrixThomSpectralData.cutFrame_final (S : MatrixThomSpectralData A B D ε) :
    S.cutFrame * S.cutFrameᴴ = S.cut := matrixProjectionFinFrame_final S.cut_projection

noncomputable def MatrixThomSpectralData.cutSourceRepresentation
    (S : MatrixThomSpectralData A B D ε) : B →⋆ₐ[ℂ] CMatrix S.cut.rank :=
  matrixReducingRepresentation B S.sourceRep S.cutFrame S.cutFrame_initial
    (fun X hX => by rw [S.cutFrame_final]; exact S.cut_commutes_source X hX)

noncomputable def MatrixThomSpectralData.cutCommutantRepresentation
    (S : MatrixThomSpectralData A B D ε) :
    StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) →⋆ₐ[ℂ] CMatrix S.cut.rank :=
  matrixReducingRepresentation _ S.commutantRep S.cutFrame S.cutFrame_initial
    (fun X hX => by rw [S.cutFrame_final]; exact S.cut_commutes_commutant X hX)

theorem MatrixThomSpectralData.cutSourceRepresentation_apply
    (S : MatrixThomSpectralData A B D ε) (X : B) :
    S.cutSourceRepresentation X = S.cutFrameᴴ * S.sourceRep X * S.cutFrame := rfl

theorem MatrixThomSpectralData.cutCommutantRepresentation_apply
    (S : MatrixThomSpectralData A B D ε) (Y : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    S.cutCommutantRepresentation Y = S.cutFrameᴴ * S.commutantRep Y * S.cutFrame := rfl

theorem MatrixThomSpectralData.cutSourceRepresentation_intertwines
    (S : MatrixThomSpectralData A B D ε) (X : B) :
    S.sourceRep X * S.cutFrame = S.cutFrame * S.cutSourceRepresentation X := by
  apply matrixFrame_reducing_intertwines S.cutFrame_initial
  rw [S.cutFrame_final]
  exact S.cut_commutes_source X X.property

theorem MatrixThomSpectralData.cutCommutantRepresentation_intertwines
    (S : MatrixThomSpectralData A B D ε) (Y : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    S.commutantRep Y * S.cutFrame = S.cutFrame * S.cutCommutantRepresentation Y := by
  apply matrixFrame_reducing_intertwines S.cutFrame_initial
  rw [S.cutFrame_final]
  exact S.cut_commutes_commutant Y Y.property

theorem MatrixThomSpectralData.cutRepresentations_commute
    (S : MatrixThomSpectralData A B D ε) (X : B) (Y : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    S.cutSourceRepresentation X * S.cutCommutantRepresentation Y =
      S.cutCommutantRepresentation Y * S.cutSourceRepresentation X := by
  apply matrixFrame_compressions_commute S.cutFrame_initial
  · rw [S.cutFrame_final]; exact S.cut_commutes_source X X.property
  · rw [S.cutFrame_final]; exact S.cut_commutes_commutant Y Y.property
  · exact S.representations_commute X Y

noncomputable def MatrixThomSpectralData.correctedSourceAlgebra
    (S : MatrixThomSpectralData A B D ε) : StarSubalgebra ℂ (CMatrix S.cut.rank) :=
  S.cutSourceRepresentation.range

noncomputable def MatrixThomSpectralData.correctedTargetAlgebra
    (S : MatrixThomSpectralData A B D ε) : StarSubalgebra ℂ (CMatrix S.cut.rank) :=
  StarSubalgebra.centralizer ℂ (S.cutCommutantRepresentation.range : Set (CMatrix S.cut.rank))

theorem MatrixThomSpectralData.correctedSourceAlgebra_le_target
    (S : MatrixThomSpectralData A B D ε) : S.correctedSourceAlgebra ≤ S.correctedTargetAlgebra := by
  intro X hX
  have hx : ∃ b : B, S.cutSourceRepresentation b = X := hX
  obtain ⟨b, rfl⟩ := hx
  apply (mem_matrixSubalgebraCommutant_iff S.cutCommutantRepresentation.range _).mpr
  intro Y hY
  have hy : ∃ a, S.cutCommutantRepresentation a = Y := hY
  obtain ⟨a, rfl⟩ := hy
  exact (S.cutRepresentations_commute b a).symm

end ThomGame.Analysis
