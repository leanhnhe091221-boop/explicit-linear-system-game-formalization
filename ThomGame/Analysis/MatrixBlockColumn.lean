module

public import ThomGame.Analysis.MatrixCornerUnitary
public import Mathlib.Data.Matrix.Block

/-!
# Columns and unitaries on finite sums of possibly unequal spaces

Dependent sum indices realize the actual auxiliary space. The column
Gram matrix and its normalized energy are exactly the sums over blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ ι : Type*} {κ : μ → Type*} [Fintype μ] [Fintype ι]
  [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι] [∀ i, DecidableEq (κ i)]

omit [Fintype μ] [Fintype ι] [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] in
def matrixBlockColumn (A : ∀ i, Matrix (κ i) ι ℂ) : Matrix (Σ i, κ i) ι ℂ :=
  fun i j => A i.1 i.2 j

omit [Fintype ι] [DecidableEq μ] [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
theorem matrixBlockColumn_gram (A : ∀ i, Matrix (κ i) ι ℂ) :
    (matrixBlockColumn A)ᴴ * matrixBlockColumn A = ∑ i, (A i)ᴴ * A i := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matrixBlockColumn,
    Fintype.sum_sigma, Matrix.sum_apply]

omit [DecidableEq μ] [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
theorem rectHSNorm_blockColumn_sq (r : Nat) (A : ∀ i, Matrix (κ i) ι ℂ) :
    rectHSNorm r (matrixBlockColumn A) ^ 2 = ∑ i, rectHSNorm r (A i) ^ 2 := by
  simp only [rectHSNorm_sq, matrixBlockColumn, Fintype.sum_sigma, Finset.sum_div]

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
theorem matrixBlockDiagonal_mul_column (V : ∀ i, Matrix (κ i) (κ i) ℂ)
    (A : ∀ i, Matrix (κ i) ι ℂ) :
    Matrix.blockDiagonal' V * matrixBlockColumn A = matrixBlockColumn (fun i => V i * A i) := by
  ext ⟨i, k⟩ j
  simp only [Matrix.mul_apply, Fintype.sum_sigma, Matrix.blockDiagonal'_apply',
    matrixBlockColumn]
  simp

omit [Fintype μ] [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] in
theorem matrixBlockColumn_mul (A : ∀ i, Matrix (κ i) ι ℂ) (U : Matrix ι ι ℂ) :
    matrixBlockColumn A * U = matrixBlockColumn (fun i => A i * U) := rfl

omit [Fintype μ] [Fintype ι] [∀ i, Fintype (κ i)] [DecidableEq μ] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] in
theorem matrixBlockColumn_sub (A B : ∀ i, Matrix (κ i) ι ℂ) :
    matrixBlockColumn A - matrixBlockColumn B = matrixBlockColumn (fun i => A i - B i) := rfl

omit [Fintype ι] [DecidableEq ι] in
noncomputable def matrixBlockUnitary (V : ∀ i, Matrix.unitaryGroup (κ i) ℂ) :
    Matrix.unitaryGroup (Σ i, κ i) ℂ := by
  refine ⟨Matrix.blockDiagonal' (fun i => (V i).val), Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (Matrix.blockDiagonal' (fun i => (V i).val))ᴴ * Matrix.blockDiagonal' (fun i => (V i).val) = 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have hv : (fun i => (V i).valᴴ * (V i).val) = (1 : ∀ i, Matrix (κ i) (κ i) ℂ) :=
    funext fun i => (V i).prop.1
  rw [hv, Matrix.blockDiagonal'_one]

theorem matrixIntertwiningEnergy_blockColumn {h : Nat} (r : Nat)
    (U : Fin h → Matrix.unitaryGroup ι ℂ) (V : Fin h → ∀ i, Matrix.unitaryGroup (κ i) ℂ)
    (A : ∀ i, Matrix (κ i) ι ℂ) :
    matrixIntertwiningEnergy r U (fun j => matrixBlockUnitary (V j)) (matrixBlockColumn A) =
      ∑ i, matrixIntertwiningEnergy r U (fun j => V j i) (A i) := by
  unfold matrixIntertwiningEnergy
  change lazyMarkovWeight h * ∑ j, rectHSNorm r
    (Matrix.blockDiagonal' (fun i => (V j i).val) * matrixBlockColumn A - matrixBlockColumn A * (U j).val) ^ 2 = _
  simp_rw [matrixBlockDiagonal_mul_column, matrixBlockColumn_mul, matrixBlockColumn_sub,
    rectHSNorm_blockColumn_sq]
  rw [Finset.sum_comm, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def matrixBlockLabel (i : μ) : Matrix (Σ i, κ i) (Σ i, κ i) ℂ :=
  Matrix.diagonal (fun k => if k.1 = i then 1 else 0)

omit [Fintype ι] [DecidableEq ι] in
theorem matrixBlockLabel_projection (i : μ) : IsStarProjection (matrixBlockLabel (κ := κ) i) := by
  constructor
  · show matrixBlockLabel i * matrixBlockLabel i = matrixBlockLabel (κ := κ) i
    simp only [matrixBlockLabel, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    split_ifs <;> simp
  · show (matrixBlockLabel (κ := κ) i)ᴴ = matrixBlockLabel i
    simp only [matrixBlockLabel, Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    split_ifs with h <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixBlockLabel_orthogonal {i j : μ} (hij : i ≠ j) :
    matrixBlockLabel (κ := κ) i * matrixBlockLabel j = 0 := by
  simp only [matrixBlockLabel, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_zero]
  congr 1
  funext k
  by_cases hi : k.1 = i
  · simp [hi, hij]
  · simp [hi]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] in
theorem matrixBlockLabel_sum : ∑ i, matrixBlockLabel (κ := κ) i = 1 := by
  ext k l
  by_cases h : k = l
  · subst l
    simp [Matrix.sum_apply, matrixBlockLabel]
  · simp [Matrix.sum_apply, matrixBlockLabel, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixBlockLabel_commute (V : ∀ i, Matrix (κ i) (κ i) ℂ) (i : μ) :
    Commute (Matrix.blockDiagonal' V) (matrixBlockLabel i) := by
  show Matrix.blockDiagonal' V * matrixBlockLabel i = matrixBlockLabel i * Matrix.blockDiagonal' V
  ext ⟨j, k⟩ ⟨j', k'⟩
  simp only [matrixBlockLabel, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : j = j'
  · subst j'
    split_ifs <;> simp
  · simp only [Matrix.blockDiagonal'_apply_ne V k k' h, zero_mul, mul_zero]

end ThomGame.Analysis
