module

public import ThomGame.Analysis.MatrixPinchingDefect
public import ThomGame.Analysis.MatrixExponentialMixing

/-!
# Real parameters on an orthogonal projection partition

The actual coefficient sum commutes with each block and is an
operator-norm contraction on the cube [-1,1]. Updating one parameter
is an affine commuting direction of the exponential range.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

noncomputable def matrixProjectionParameter (E : μ → Matrix ι ι ℂ) (s : μ → ℝ) : Matrix ι ι ℂ :=
  ∑ i, s i • E i

omit [DecidableEq ι] [DecidableEq μ] in
theorem matrixProjectionParameter_isHermitian (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (s : μ → ℝ) :
    Matrix.IsHermitian (matrixProjectionParameter E s) := by
  show (matrixProjectionParameter E s)ᴴ = _
  simp only [matrixProjectionParameter, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_trivial, fun i => (hE i).isSelfAdjoint.isHermitian.eq]

omit [DecidableEq μ] in
theorem matrixProjectionParameter_block_right (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (s : μ → ℝ) (j : μ) : matrixProjectionParameter E s * E j = s j • E j := by
  rw [matrixProjectionParameter, Matrix.sum_mul, Finset.sum_eq_single j]
  · rw [Matrix.smul_mul, (hE j).isIdempotentElem.eq]
  · intro i _ hij
    rw [Matrix.smul_mul, horth i j hij, smul_zero]
  · simp

omit [DecidableEq μ] in
theorem matrixProjectionParameter_commute (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (s : μ → ℝ) (j : μ) : Commute (matrixProjectionParameter E s) (E j) := by
  have he := matrixProjectionParameter_block_right E hE horth s j
  have hf := congrArg Matrix.conjTranspose he
  simp only [Matrix.conjTranspose_mul, (hE j).isSelfAdjoint.isHermitian.eq,
    (matrixProjectionParameter_isHermitian E hE s).eq, Matrix.conjTranspose_smul, star_trivial] at hf
  exact he.trans hf.symm

omit [DecidableEq μ] in
theorem matrixProjectionParameter_square (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (s : μ → ℝ) : matrixProjectionParameter E s * matrixProjectionParameter E s = ∑ i, (s i) ^ 2 • E i := by
  change matrixProjectionParameter E s * (∑ i, s i • E i) = _
  rw [Matrix.mul_sum]
  simp only [Matrix.mul_smul, matrixProjectionParameter_block_right E hE horth s, smul_smul, pow_two]

omit [DecidableEq μ] in
theorem matrixProjectionParameter_norm_le_one (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) (s : μ → ℝ) (hs : ∀ i, |s i| ≤ 1) :
    ‖matrixProjectionParameter E s‖ ≤ 1 := by
  have hle : matrixProjectionParameter E s * matrixProjectionParameter E s ≤ 1 := by
    rw [matrixProjectionParameter_square E hE horth]
    have he : 0 ≤ ∑ i, (1 - (s i) ^ 2) • E i := by
      apply Finset.sum_nonneg
      intro i _
      have hsq := sq_le_sq₀ (abs_nonneg (s i)) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr (hs i)
      have hi : 0 ≤ 1 - (s i) ^ 2 := by simpa only [sq_abs, one_pow, sub_nonneg] using hsq
      exact smul_nonneg hi (hE i).nonneg
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, hsum] at he
    exact sub_nonneg.mp he
  have hA := (matrixProjectionParameter_isHermitian E hE s).isSelfAdjoint
  have hpos : 0 ≤ matrixProjectionParameter E s * matrixProjectionParameter E s := by
    simpa only [hA.star_eq] using star_mul_self_nonneg (matrixProjectionParameter E s)
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mpr hle
  rw [hA.norm_mul_self] at hn
  nlinarith [norm_nonneg (matrixProjectionParameter E s)]

omit [DecidableEq ι] [DecidableEq μ] in
theorem matrixProjectionParameter_commute_of_blocks (E : μ → Matrix ι ι ℂ) (s : μ → ℝ)
    (W : Matrix ι ι ℂ) (hW : ∀ i, W * E i = E i * W) :
    W * matrixProjectionParameter E s = matrixProjectionParameter E s * W := by
  simp only [matrixProjectionParameter, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, hW]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjectionParameter_update (E : μ → Matrix ι ι ℂ) (s : μ → ℝ) (j : μ) (a : ℝ) :
    matrixProjectionParameter E (Function.update s j a) =
      matrixProjectionParameter E (Function.update s j 0) + a • E j := by
  have he (i : μ) : Function.update s j a i • E i =
      Function.update s j 0 i • E i + if i = j then a • E j else 0 := by
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  simp only [matrixProjectionParameter, he, Finset.sum_add_distrib]
  simp

end ThomGame.Analysis
