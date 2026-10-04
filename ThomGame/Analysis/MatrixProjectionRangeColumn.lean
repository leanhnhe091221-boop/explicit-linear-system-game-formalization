module

public import ThomGame.Analysis.MatrixBlockColumn

/-!
# The actual column into the sum of projection ranges

Orthonormal eigenvector frames realize K = direct sum q_i H without
padding its dimension. Compressed polar unitaries give I(F) bounded by
the total boundary energy of the projections, with both local errors.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq μ] [DecidableEq ι]

omit [Fintype μ] [DecidableEq μ] in
abbrev MatrixProjectionRangeIndex {q : Matrix ι ι ℂ} (hq : IsStarProjection q) :=
  {i // hq.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0}

abbrev MatrixProjectionSumIndex {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i)) :=
  Σ i, MatrixProjectionRangeIndex (hq i)

noncomputable def matrixProjectionColumn {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i)) :
    Matrix (MatrixProjectionSumIndex hq) ι ℂ :=
  matrixBlockColumn (fun i => (matrixProjectionFrame (hq i))ᴴ)

omit [DecidableEq μ] in
theorem matrixProjectionColumn_gram {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i)) :
    (matrixProjectionColumn hq)ᴴ * matrixProjectionColumn hq = ∑ i, q i := by
  rw [matrixProjectionColumn, matrixBlockColumn_gram]
  simp only [Matrix.conjTranspose_conjTranspose, matrixProjectionFrame_final]

omit [DecidableEq μ] in
theorem matrixProjectionSumIndex_card {q : μ → Matrix ι ι ℂ} (hq : ∀ i, IsStarProjection (q i)) :
    Fintype.card (MatrixProjectionSumIndex hq) = ∑ i, (q i).rank := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (hq i).isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs.symm

omit [Fintype ι] [DecidableEq μ] [DecidableEq ι] in
theorem matrixProjectionSumIndex_card_le_three {d : Nat} [NeZero d]
    {q : μ → CMatrix d} (hq : ∀ i, IsStarProjection (q i))
    (hsum : ∑ i, matrixTraceReal d (q i) ≤ 3) :
    Fintype.card (MatrixProjectionSumIndex hq) ≤ 3 * d := by
  rw [matrixProjectionSumIndex_card]
  simp_rw [matrixTraceReal_projection_rank d (hq _)] at hsum
  rw [← Finset.sum_div] at hsum
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have he := (div_le_iff₀ hd).mp hsum
  exact_mod_cast he

omit [Fintype μ] [DecidableEq μ] in
noncomputable def matrixProjectionRangeUnitary (r : Nat) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) (u : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (MatrixProjectionRangeIndex hq) ℂ :=
  Classical.choose (exists_matrixFrameCompressionUnitary r hq
    (matrixProjectionFrame_initial hq) (matrixProjectionFrame_final hq) u)

omit [Fintype μ] [DecidableEq μ] in
theorem matrixProjectionRangeUnitary_errors (r : Nat) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) (u : Matrix.unitaryGroup ι ℂ) :
    rectHSNorm r ((matrixProjectionRangeUnitary r hq u).val * (matrixProjectionFrame hq)ᴴ -
      (matrixProjectionFrame hq)ᴴ * u.val) ^ 2 ≤ rectHSNorm r (u.val * q - q * u.val) ^ 2 ∧
    rectHSNorm r (u.val * matrixProjectionFrame hq -
      matrixProjectionFrame hq * (matrixProjectionRangeUnitary r hq u).val) ^ 2 ≤
      rectHSNorm r (u.val * q - q * u.val) ^ 2 :=
  Classical.choose_spec (exists_matrixFrameCompressionUnitary r hq
    (matrixProjectionFrame_initial hq) (matrixProjectionFrame_final hq) u)

noncomputable def matrixProjectionBlockUnitary (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) (u : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (MatrixProjectionSumIndex hq) ℂ :=
  matrixBlockUnitary (fun i => matrixProjectionRangeUnitary r (hq i) u)

theorem matrixProjectionBlockUnitary_commute (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) (u : Matrix.unitaryGroup ι ℂ) (i : μ) :
    Commute (matrixProjectionBlockUnitary r hq u).val
      (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i) :=
  matrixBlockLabel_commute _ i

theorem matrixProjectionColumn_energy_le {h : Nat} (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → Matrix.unitaryGroup ι ℂ) :
    matrixIntertwiningEnergy r U (fun j => matrixProjectionBlockUnitary r hq (U j))
      (matrixProjectionColumn hq) ≤ ∑ i, matrixIntertwiningEnergy r U U (q i) := by
  rw [matrixProjectionColumn]
  change matrixIntertwiningEnergy r U
    (fun j => matrixBlockUnitary (fun i => matrixProjectionRangeUnitary r (hq i) (U j)))
      (matrixBlockColumn (fun i => (matrixProjectionFrame (hq i))ᴴ)) ≤ _
  rw [matrixIntertwiningEnergy_blockColumn]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (lazyMarkovWeight_nonneg h)
  apply Finset.sum_le_sum
  intro j _
  exact (matrixProjectionRangeUnitary_errors r (hq i) (U j)).1

end ThomGame.Analysis
