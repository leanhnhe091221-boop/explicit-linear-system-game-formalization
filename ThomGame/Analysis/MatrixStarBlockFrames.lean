module

public import ThomGame.Analysis.MatrixStarBlockUnits
public import ThomGame.Analysis.MatrixProjectionFinFrame

/-!
# Actual orthonormal frames for the simple-block copies

Start with a frame of the first diagonal projection and transport it by
the star matrix units. The column count is exactly the intrinsic
multiplicity, including zero multiplicity in nonfaithful representations.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

noncomputable def matrixStarBlockBaseFrame (i : Fin P.count) :
    Matrix (Fin m) (Fin (matrixStarRepresentationMultiplicity A P ρ i)) ℂ :=
  matrixProjectionFinFrame (matrixStarRepresentationUnit_diagonal_projection A P ρ i ⟨0, P.size_pos i⟩)

theorem matrixStarBlockBaseFrame_initial (i : Fin P.count) :
    (matrixStarBlockBaseFrame A P ρ i)ᴴ * matrixStarBlockBaseFrame A P ρ i = 1 :=
  matrixProjectionFinFrame_initial _

theorem matrixStarBlockBaseFrame_final (i : Fin P.count) :
    matrixStarBlockBaseFrame A P ρ i * (matrixStarBlockBaseFrame A P ρ i)ᴴ =
      ρ (matrixStarBlockUnit A P i ⟨0, P.size_pos i⟩ ⟨0, P.size_pos i⟩) :=
  matrixProjectionFinFrame_final _

theorem matrixStarBlockBaseFrame_support (i : Fin P.count) :
    ρ (matrixStarBlockUnit A P i ⟨0, P.size_pos i⟩ ⟨0, P.size_pos i⟩) *
      matrixStarBlockBaseFrame A P ρ i = matrixStarBlockBaseFrame A P ρ i := by
  rw [← matrixStarBlockBaseFrame_final, Matrix.mul_assoc, matrixStarBlockBaseFrame_initial, Matrix.mul_one]

noncomputable def matrixStarBlockFrame (i : Fin P.count) (a : Fin (P.size i)) :
    Matrix (Fin m) (Fin (matrixStarRepresentationMultiplicity A P ρ i)) ℂ :=
  ρ (matrixStarBlockUnit A P i a ⟨0, P.size_pos i⟩) * matrixStarBlockBaseFrame A P ρ i

theorem matrixStarBlockFrame_mul_adjoint (i : Fin P.count) (a b : Fin (P.size i)) :
    matrixStarBlockFrame A P ρ i a * (matrixStarBlockFrame A P ρ i b)ᴴ =
      ρ (matrixStarBlockUnit A P i a b) := by
  rw [matrixStarBlockFrame, matrixStarBlockFrame, Matrix.conjTranspose_mul, matrixStarRepresentationUnit_adjoint]
  calc
    _ = ρ (matrixStarBlockUnit A P i a ⟨0, P.size_pos i⟩) *
        (matrixStarBlockBaseFrame A P ρ i * (matrixStarBlockBaseFrame A P ρ i)ᴴ) *
        ρ (matrixStarBlockUnit A P i ⟨0, P.size_pos i⟩ b) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [matrixStarBlockBaseFrame_final]
      simp only [← map_mul, matrixStarBlockUnit_mul, ite_true]

theorem matrixStarBlockFrame_initial (i : Fin P.count) (a : Fin (P.size i)) :
    (matrixStarBlockFrame A P ρ i a)ᴴ * matrixStarBlockFrame A P ρ i a = 1 := by
  rw [matrixStarBlockFrame, Matrix.conjTranspose_mul, matrixStarRepresentationUnit_adjoint]
  calc
    _ = (matrixStarBlockBaseFrame A P ρ i)ᴴ *
        (ρ (matrixStarBlockUnit A P i ⟨0, P.size_pos i⟩ a) *
          ρ (matrixStarBlockUnit A P i a ⟨0, P.size_pos i⟩)) * matrixStarBlockBaseFrame A P ρ i := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      simp only [← map_mul, matrixStarBlockUnit_mul, ite_true]
      rw [Matrix.mul_assoc,
        matrixStarBlockBaseFrame_support, matrixStarBlockBaseFrame_initial]

theorem matrixStarBlockFrames_final_sum :
    ∑ i, ∑ a, matrixStarBlockFrame A P ρ i a * (matrixStarBlockFrame A P ρ i a)ᴴ = 1 := by
  simp only [matrixStarBlockFrame_mul_adjoint, ← map_sum, matrixStarBlockUnit_total_diagonal_sum, map_one]

end ThomGame.Analysis
