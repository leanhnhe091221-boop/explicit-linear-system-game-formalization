module

public import ThomGame.Analysis.MatrixALTCoordinateAlgebra
public import ThomGame.Analysis.MatrixCompletedExpectationError

/-!
# Finite ALT reconstruction with a dimension-independent mixed-norm bound

The algebra and its expectation are constructed from the actual channel.
No spectral bands or matrix-unit existence are supplied as assumptions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

theorem matrixALT_trace_loss_error_bound (rho p q : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1)
    (hp : p ≤ 64 * rho ^ 2) (hq : q ≤ 64 * rho ^ 2 + 2 * rho) :
    113 * Real.sqrt rho + Real.sqrt (2 * p) + Real.sqrt q ≤ 134 * Real.sqrt rho := by
  have hrsq : rho ^ 2 ≤ rho := by nlinarith
  have hploss : Real.sqrt (2 * p) ≤ 12 * Real.sqrt rho := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hrho]
      nlinarith
  have hqloss : Real.sqrt q ≤ 9 * Real.sqrt rho := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hrho]
      nlinarith
  linarith

theorem exists_matrixALT_approximating_algebra {d : Nat} [NeZero d]
    {μ : Type*} [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hdelta : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ rho ^ 4) :
    ∃ A : StarSubalgebra ℂ (CMatrix d), matrixPartitionScalarAlgebra E ≤ A ∧
      matrixMixedNorm (F.toLinearMap - matrixTraceProjection A) ≤ 134 * Real.sqrt rho := by
  obtain ⟨S, _, W, A, _, hpmass, hQ, _, hQmass, _, _, hsupport, _, _, _, hD, _, hexpect, hbound⟩ :=
    exists_matrixALT_coordinate_algebra F hF htrace hpair E hE hne horth hsum hbimod
      rho hrho hsmall hsigma hdelta
  have hinv (i j : S) : ∀ X ∈ matrixRectangleSubmodule (E i.val) (E j.val),
      F.toLinearMap X ∈ matrixRectangleSubmodule (E i.val) (E j.val) :=
    matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap hbimod
      (E i.val) (E j.val) (matrixPartitionScalarAlgebra_projection_mem E i.val)
        (matrixPartitionScalarAlgebra_projection_mem E j.val)
  have horthS : Pairwise (fun i j : S => E i.val * E j.val = 0) := by
    intro i j hij
    exact horth (fun he => hij (Subtype.ext he))
  have hb := matrixUnitSpan_completed_expectation_bound F.toLinearMap (matrixUCP_hsNorm_le F hF htrace)
    (fun i : S => E i.val) W (fun i => hE i.val) horthS hsupport hinv (113 * Real.sqrt rho)
    (by positivity) (fun i j => hbound i j (hsupport i j).1 (hsupport i j).2)
    (∑ i, W i i) hQ A hexpect
  exact ⟨A, hD, hb.trans (matrixALT_trace_loss_error_bound rho _ _ hrho.le (by linarith) hpmass hQmass)⟩

end ThomGame.Analysis
