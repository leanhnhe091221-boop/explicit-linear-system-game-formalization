module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationMultiplicity

/-!
# Joint multiplicities of two commuting actual representations

The nonnegative integer table is constructed from ranks of products of
diagonal matrix units. Exact row and column formulas follow from matrix
unit multiplication and trace cyclicity. No multiplicity table or
dimension identity is supplied as an assumption.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrixCommutingProducts_mul {m : Nat} (X Y Z W : CMatrix m) (hYZ : Y * Z = Z * Y) :
    (X * Y) * (Z * W) = (X * Z) * (Y * W) := by
  calc
    (X * Y) * (Z * W) = X * (Y * Z) * W := by simp only [Matrix.mul_assoc]
    _ = X * (Z * Y) * W := by rw [hYZ]
    _ = (X * Z) * (Y * W) := by simp only [Matrix.mul_assoc]

variable {d e m : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (B : StarSubalgebra ℂ (CMatrix e))
    (S : MatrixSubalgebraAlgebraicBlocks A) (R : MatrixSubalgebraAlgebraicBlocks B)
    (ρ : A →ₐ[ℂ] CMatrix m) (σ : B →ₐ[ℂ] CMatrix m)
    (hcomm : ∀ X Y, ρ X * σ Y = σ Y * ρ X)

noncomputable def matrixAlgebraicJointMultiplicity (i : Fin S.count) (j : Fin R.count) : Nat :=
  (ρ (matrixAlgebraicBlockUnit A S i ⟨0, S.size_pos i⟩ ⟨0, S.size_pos i⟩) *
    σ (matrixAlgebraicBlockUnit B R j ⟨0, R.size_pos j⟩ ⟨0, R.size_pos j⟩)).rank

include hcomm

theorem matrixAlgebraicJointUnit_mul (i : Fin S.count) (j : Fin R.count)
    (a c a' : Fin (S.size i)) (b f b' : Fin (R.size j)) :
    (ρ (matrixAlgebraicBlockUnit A S i a c) * σ (matrixAlgebraicBlockUnit B R j b f)) *
        (ρ (matrixAlgebraicBlockUnit A S i c a') * σ (matrixAlgebraicBlockUnit B R j f b')) =
      ρ (matrixAlgebraicBlockUnit A S i a a') * σ (matrixAlgebraicBlockUnit B R j b b') := by
  rw [matrixCommutingProducts_mul _ _ _ _ (hcomm _ _).symm]
  simp only [← map_mul, matrixAlgebraicBlockUnit_mul_same]

theorem matrixAlgebraicJoint_diagonal_idempotent (i : Fin S.count) (j : Fin R.count)
    (a : Fin (S.size i)) (b : Fin (R.size j)) :
    IsIdempotentElem (ρ (matrixAlgebraicBlockUnit A S i a a) * σ (matrixAlgebraicBlockUnit B R j b b)) :=
  matrixAlgebraicJointUnit_mul A B S R ρ σ hcomm i j a a a b b b

theorem matrixAlgebraicJoint_diagonal_rank_eq (i : Fin S.count) (j : Fin R.count)
    (a c : Fin (S.size i)) (b f : Fin (R.size j)) :
    (ρ (matrixAlgebraicBlockUnit A S i a a) * σ (matrixAlgebraicBlockUnit B R j b b)).rank =
      (ρ (matrixAlgebraicBlockUnit A S i c c) * σ (matrixAlgebraicBlockUnit B R j f f)).rank := by
  apply matrixIdempotent_rank_eq_of_trace_eq
    (matrixAlgebraicJoint_diagonal_idempotent A B S R ρ σ hcomm i j a b)
    (matrixAlgebraicJoint_diagonal_idempotent A B S R ρ σ hcomm i j c f)
  have he := Matrix.trace_mul_comm
    (ρ (matrixAlgebraicBlockUnit A S i a c) * σ (matrixAlgebraicBlockUnit B R j b f))
    (ρ (matrixAlgebraicBlockUnit A S i c a) * σ (matrixAlgebraicBlockUnit B R j f b))
  simpa only [matrixAlgebraicJointUnit_mul A B S R ρ σ hcomm] using he

theorem matrixAlgebraicJoint_diagonal_rank (i : Fin S.count) (j : Fin R.count)
    (a : Fin (S.size i)) (b : Fin (R.size j)) :
    (ρ (matrixAlgebraicBlockUnit A S i a a) * σ (matrixAlgebraicBlockUnit B R j b b)).rank =
      matrixAlgebraicJointMultiplicity A B S R ρ σ i j :=
  matrixAlgebraicJoint_diagonal_rank_eq A B S R ρ σ hcomm i j
    a ⟨0, S.size_pos i⟩ b ⟨0, R.size_pos j⟩

theorem matrixAlgebraicJointMultiplicity_row (i : Fin S.count) :
    matrixAlgebraicRepresentationMultiplicity A S ρ i =
      ∑ j, R.size j * matrixAlgebraicJointMultiplicity A B S R ρ σ i j := by
  let a : Fin (S.size i) := ⟨0, S.size_pos i⟩
  let X := ρ (matrixAlgebraicBlockUnit A S i a a)
  have hinner (j : Fin R.count) :
      ∑ b, X * σ (matrixAlgebraicBlockUnit B R j b b) = X * σ (matrixAlgebraicBlockSupport B R j) := by
    rw [← Finset.mul_sum, ← map_sum, matrixAlgebraicBlockUnit_diagonal_sum]
  have hs : ∑ j, ∑ b, X * σ (matrixAlgebraicBlockUnit B R j b b) = X := by
    simp_rw [hinner]
    rw [← Finset.mul_sum, ← map_sum, matrixAlgebraicBlockSupport_sum, map_one, Matrix.mul_one]
  have htr (j : Fin R.count) (b : Fin (R.size j)) :
      (X * σ (matrixAlgebraicBlockUnit B R j b b)).trace =
        (matrixAlgebraicJointMultiplicity A B S R ρ σ i j : ℂ) := by
    rw [matrixIdempotent_trace_eq_rank (matrixAlgebraicJoint_diagonal_idempotent A B S R ρ σ hcomm i j a b),
      matrixAlgebraicJoint_diagonal_rank A B S R ρ σ hcomm]
  have he := congrArg Matrix.trace hs
  simp only [Matrix.trace_sum, htr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  rw [matrixIdempotent_trace_eq_rank (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i a)] at he
  exact_mod_cast he.symm

theorem matrixAlgebraicJointMultiplicity_swap (i : Fin S.count) (j : Fin R.count) :
    matrixAlgebraicJointMultiplicity A B S R ρ σ i j =
      matrixAlgebraicJointMultiplicity B A R S σ ρ j i := by
  unfold matrixAlgebraicJointMultiplicity
  rw [hcomm]

theorem matrixAlgebraicJointMultiplicity_column (j : Fin R.count) :
    matrixAlgebraicRepresentationMultiplicity B R σ j =
      ∑ i, S.size i * matrixAlgebraicJointMultiplicity A B S R ρ σ i j := by
  have he := matrixAlgebraicJointMultiplicity_row B A R S σ ρ (fun Y X => (hcomm X Y).symm) j
  simpa only [← matrixAlgebraicJointMultiplicity_swap A B S R ρ σ hcomm] using he

theorem matrixAlgebraicJointMultiplicity_dimension :
    m = ∑ i, ∑ j, S.size i * R.size j * matrixAlgebraicJointMultiplicity A B S R ρ σ i j := by
  calc
    m = ∑ i, S.size i * matrixAlgebraicRepresentationMultiplicity A S ρ i :=
      matrixAlgebraicRepresentation_dimension A S ρ
    _ = _ := by
      simp only [matrixAlgebraicJointMultiplicity_row A B S R ρ σ hcomm, Finset.mul_sum, Nat.mul_assoc]

end ThomGame.Analysis
