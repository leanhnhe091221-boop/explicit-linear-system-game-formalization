module

public import ThomGame.Analysis.MatrixHalfSpectralCut

/-!
# Rounding the actual block pinching at one half

The spectral projection commutes with every partition block. Its
squared distance to the original projection and its trace error
are both bounded by twice the original pinching defect.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

theorem matrixBlockPinch_eq_of_commute (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (hsum : ∑ i, E i = 1)
    (X : Matrix ι ι ℂ) (hX : ∀ i, Commute (E i) X) : matrixBlockPinch E X = X := by
  simp only [matrixBlockPinch, fun i => (hX i).eq, Matrix.mul_assoc,
    fun i => (hE i).isIdempotentElem.eq]
  rw [← Matrix.mul_sum, hsum, Matrix.mul_one]

theorem matrixHalfProjection_pinching_commute (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (j : μ) :
    Commute (E j) (matrixHalfProjection (matrixBlockPinch E P)) :=
  matrixHalfProjection_commute (matrixBlockPinch_isHermitian E hE hP.isSelfAdjoint.isHermitian)
    (matrixBlockPinch_commute E hE horth j P)

theorem matrixHalfProjection_pinching_fixed (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    matrixBlockPinch E (matrixHalfProjection (matrixBlockPinch E P)) =
      matrixHalfProjection (matrixBlockPinch E P) :=
  matrixBlockPinch_eq_of_commute E hE hsum _ (matrixHalfProjection_pinching_commute E hE horth hP)

theorem rectHSNorm_pinching_projection_distance (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (hsum : ∑ i, E i = 1)
    {P Q : Matrix ι ι ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hfix : matrixBlockPinch E Q = Q) :
    rectHSNorm r (P - Q) ^ 2 = matrixTraceReal r
      (matrixBlockPinch E P + Q - (2 : ℝ) • (matrixBlockPinch E P * Q)) := by
  rw [rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian hQ.isSelfAdjoint.isHermitian,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq,
    matrixTraceReal_sub, matrixTraceReal_add, matrixTraceReal_real_smul,
    matrixBlockPinch_trace r E hE hsum, matrixBlockPinch_trace_pairing, hfix]
  ring

theorem matrixHalfProjection_pinching_distance_le (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    rectHSNorm r (P - matrixHalfProjection (matrixBlockPinch E P)) ^ 2 ≤
      2 * rectHSNorm r (P - matrixBlockPinch E P) ^ 2 := by
  rw [rectHSNorm_pinching_projection_distance r E hE hsum hP (matrixHalfProjection_isStarProjection _)
    (matrixHalfProjection_pinching_fixed E hE horth hsum hP),
    rectHSNorm_pinching_defect_eq_trace r E hE horth hsum hP]
  have hb := matrixBlockPinch_projection_bounds E hE hsum hP
  have he := matrixTraceReal_mono r (matrixHalfProjection_order_bounds hb.1 hb.2).2.2
  simpa only [matrixTraceReal_real_smul] using he

theorem matrixHalfProjection_pinching_trace_error_le (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    |matrixTraceReal r (matrixHalfProjection (matrixBlockPinch E P)) - matrixTraceReal r P| ≤
      2 * rectHSNorm r (P - matrixBlockPinch E P) ^ 2 := by
  rw [rectHSNorm_pinching_defect_eq_trace r E hE horth hsum hP]
  have hb := matrixBlockPinch_projection_bounds E hE hsum hP
  have he := matrixHalfProjection_order_bounds hb.1 hb.2
  have hup := matrixTraceReal_mono r he.1
  have hlo := matrixTraceReal_mono r he.2.1
  simp only [matrixTraceReal_sub, matrixTraceReal_real_smul, matrixBlockPinch_trace r E hE hsum] at hup hlo ⊢
  exact abs_le.mpr ⟨by linarith, hup⟩

end ThomGame.Analysis
