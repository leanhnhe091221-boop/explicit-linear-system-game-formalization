module

public import ThomGame.Analysis.MatrixColumnGoodThreshold
public import ThomGame.Analysis.MatrixPartialIsometryCompression

/-!
# Pulling the blocks of the actual column back into the original space

The original projection frames turn each block of Z into V_i. When
ZZ* commutes with the labels, their initial projections are mutually
orthogonal and the final projections lie below the prescribed q_i.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ ι : Type*} {κ : μ → Type*} [Fintype μ] [Fintype ι] [∀ i, Fintype (κ i)]
  [DecidableEq μ] [DecidableEq ι] [∀ i, DecidableEq (κ i)]

omit [Fintype μ] [Fintype ι] [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] in
def matrixBlockComponent (Z : Matrix (Σ i, κ i) ι ℂ) (i : μ) : Matrix (κ i) ι ℂ :=
  Z.submatrix (Sigma.mk i) id

omit [Fintype μ] [Fintype ι] [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] in
theorem matrixBlockColumn_components (Z : Matrix (Σ i, κ i) ι ℂ) :
    matrixBlockColumn (matrixBlockComponent Z) = Z := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem matrixBlockComponent_initial (Z : Matrix (Σ i, κ i) ι ℂ) (i : μ) :
    (matrixBlockComponent Z i)ᴴ * matrixBlockComponent Z i = Zᴴ * matrixBlockLabel i * Z := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [matrixBlockLabel, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    matrixBlockComponent, Matrix.submatrix_apply, id_eq, Fintype.sum_sigma]
  simp

theorem matrixBlockComponent_initial_projection {Z : Matrix (Σ i, κ i) ι ℂ}
    (hZ : IsStarProjection (Zᴴ * Z)) (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel i)) (i : μ) :
    IsStarProjection ((matrixBlockComponent Z i)ᴴ * matrixBlockComponent Z i) := by
  rw [matrixBlockComponent_initial]
  exact matrixPartialIsometry_pullback_projection hZ (matrixBlockLabel_projection i) (hcomm i)

theorem matrixBlockComponent_initial_orthogonal {Z : Matrix (Σ i, κ i) ι ℂ}
    (hZ : IsStarProjection (Zᴴ * Z)) (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel i))
    {i j : μ} (hij : i ≠ j) :
    ((matrixBlockComponent Z i)ᴴ * matrixBlockComponent Z i) *
      ((matrixBlockComponent Z j)ᴴ * matrixBlockComponent Z j) = 0 := by
  rw [matrixBlockComponent_initial, matrixBlockComponent_initial]
  exact matrixPartialIsometry_pullback_orthogonal hZ (hcomm j) (matrixBlockLabel_orthogonal hij)

omit [Fintype ι] [DecidableEq μ] [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
theorem matrixBlockComponent_initial_sum (Z : Matrix (Σ i, κ i) ι ℂ) :
    ∑ i, (matrixBlockComponent Z i)ᴴ * matrixBlockComponent Z i = Zᴴ * Z := by
  rw [← matrixBlockColumn_gram, matrixBlockColumn_components]

theorem matrixBlockComponent_energy {h : Nat} (r : Nat) (U : Fin h → Matrix.unitaryGroup ι ℂ)
    (V : Fin h → ∀ i, Matrix.unitaryGroup (κ i) ℂ) (Z : Matrix (Σ i, κ i) ι ℂ) :
    ∑ i, matrixIntertwiningEnergy r U (fun j => V j i) (matrixBlockComponent Z i) =
      matrixIntertwiningEnergy r U (fun j => matrixBlockUnitary (V j)) Z := by
  rw [← matrixIntertwiningEnergy_blockColumn, matrixBlockColumn_components]

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
noncomputable def matrixProjectionPiece {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    (Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ) (i : μ) : Matrix ι ι ℂ :=
  matrixProjectionFrame (hq i) * matrixBlockComponent Z i

omit [Fintype μ] [DecidableEq μ] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_initial {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    (Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ) (i : μ) :
    (matrixProjectionPiece hq Z i)ᴴ * matrixProjectionPiece hq Z i =
      (matrixBlockComponent Z i)ᴴ * matrixBlockComponent Z i := by
  rw [matrixProjectionPiece, Matrix.conjTranspose_mul]
  calc
    _ = (matrixBlockComponent Z i)ᴴ *
        ((matrixProjectionFrame (hq i))ᴴ * matrixProjectionFrame (hq i)) * matrixBlockComponent Z i := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [matrixProjectionFrame_initial, Matrix.mul_one]

omit [Fintype μ] [DecidableEq μ] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_target_mul {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    (Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ) (i : μ) :
    q i * matrixProjectionPiece hq Z i = matrixProjectionPiece hq Z i := by
  have hframe : q i * matrixProjectionFrame (hq i) = matrixProjectionFrame (hq i) := by
    calc
      _ = (matrixProjectionFrame (hq i) * (matrixProjectionFrame (hq i))ᴴ) * matrixProjectionFrame (hq i) :=
        congrArg (fun A : Matrix ι ι ℂ => A * matrixProjectionFrame (hq i)) (matrixProjectionFrame_final (hq i)).symm
      _ = _ := by rw [Matrix.mul_assoc, matrixProjectionFrame_initial, Matrix.mul_one]
  rw [matrixProjectionPiece, ← Matrix.mul_assoc, hframe]

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_partialIsometry {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    {Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ} (hZ : IsStarProjection (Zᴴ * Z))
    (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i))
    (i : μ) : IsStarProjection ((matrixProjectionPiece hq Z i)ᴴ * matrixProjectionPiece hq Z i) := by
  rw [matrixProjectionPiece_initial]
  exact matrixBlockComponent_initial_projection hZ hcomm i

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_final_le {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    {Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ} (hZ : IsStarProjection (Zᴴ * Z))
    (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i))
    (i : μ) : matrixProjectionPiece hq Z i * (matrixProjectionPiece hq Z i)ᴴ ≤ q i := by
  have hP := matrixPartialIsometry_final_projection (matrixProjectionPiece_partialIsometry hq hZ hcomm i)
  apply (hP.le_iff_mul_eq_left (hq i)).mpr
  have he : (matrixProjectionPiece hq Z i)ᴴ * q i = (matrixProjectionPiece hq Z i)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, (hq i).isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose (matrixProjectionPiece_target_mul hq Z i)
  rw [Matrix.mul_assoc, he]

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_orthogonal {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    {Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ} (hZ : IsStarProjection (Zᴴ * Z))
    (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i))
    {i j : μ} (hij : i ≠ j) :
    ((matrixProjectionPiece hq Z i)ᴴ * matrixProjectionPiece hq Z i) *
      ((matrixProjectionPiece hq Z j)ᴴ * matrixProjectionPiece hq Z j) = 0 := by
  rw [matrixProjectionPiece_initial, matrixProjectionPiece_initial]
  exact matrixBlockComponent_initial_orthogonal hZ hcomm hij

omit [DecidableEq μ] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem matrixProjectionPiece_initial_sum {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i))
    (Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ) :
    ∑ i, (matrixProjectionPiece hq Z i)ᴴ * matrixProjectionPiece hq Z i = Zᴴ * Z := by
  simp only [matrixProjectionPiece_initial, matrixBlockComponent_initial_sum]

end ThomGame.Analysis
