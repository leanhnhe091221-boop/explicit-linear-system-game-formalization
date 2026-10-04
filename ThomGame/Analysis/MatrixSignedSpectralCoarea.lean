module

public import ThomGame.Analysis.MatrixThresholdPolarDilation

/-!
# Signed coarea for actual matrix intertwiners

Two spectral bases reduce the integral to finite nonnegative weights.
The mass is the normalized squared HS norm of the intertwiner itself,
so auxiliary dimensions retain their original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectHSNorm_signedSpectral_intertwiner_weighted (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (X : Matrix ι κ ℂ) (s : ℝ) :
    rectHSNorm r (cfc (signedSpectralStep s) A * X - X * cfc (signedSpectralStep s) B) ^ 2 =
      ∑ p : ι × κ, (‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X p.1 p.2‖ ^ 2 / r) *
        (signedSpectralStep s (hA.eigenvalues p.1) - signedSpectralStep s (hB.eigenvalues p.2)) ^ 2 := by
  rw [rectHSNorm_cfc_intertwiner_sq r hA hB]
  simp only [Fintype.sum_prod_type, div_mul_eq_mul_div, ← Finset.sum_div]

theorem rectHSNorm_signedSpectral_intertwiner_intervalIntegrable (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (X : Matrix ι κ ℂ) (a b : ℝ) :
    IntervalIntegrable (fun s => rectHSNorm r
      (cfc (signedSpectralStep s) A * X - X * cfc (signedSpectralStep s) B) ^ 2) volume a b := by
  simp_rw [rectHSNorm_signedSpectral_intertwiner_weighted r hA hB]
  exact weighted_signedSpectralStep_intervalIntegrable a b _ _ _

theorem rectHSNorm_signedSpectral_intertwiner_coarea (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (X : Matrix ι κ ℂ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, rectHSNorm r (cfc (signedSpectralStep s) A * X - X * cfc (signedSpectralStep s) B) ^ 2) ≤
      2 * rectHSNorm r X * rectHSNorm r (A * X - X * B) := by
  let c : ι × κ → ℝ := fun p =>
    ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X p.1 p.2‖ ^ 2 / r
  have hc (p : ι × κ) : 0 ≤ c p := div_nonneg (sq_nonneg _) (Nat.cast_nonneg r)
  have hmass : ∑ p, c p = rectHSNorm r X ^ 2 := by
    simp only [c, Fintype.sum_prod_type, ← Finset.sum_div, ← rectHSNorm_sq, rectHSNorm_intertwiner_basis]
  have henergy : (∑ p, c p * (hA.eigenvalues p.1 - hB.eigenvalues p.2) ^ 2) =
      rectHSNorm r (A * X - X * B) ^ 2 := by
    rw [rectHSNorm_intertwiner_spectral_sq r hA hB]
    simp only [c, Fintype.sum_prod_type, div_mul_eq_mul_div, ← Finset.sum_div]
  have he := weighted_signedSpectralStep_coarea a b ha hab c
    (fun p => hA.eigenvalues p.1) (fun p => hB.eigenvalues p.2) hc
  rw [hmass, henergy, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (rectHSNorm_nonneg _ _),
    Real.sqrt_sq (rectHSNorm_nonneg _ _)] at he
  simp only [rectHSNorm_signedSpectral_intertwiner_weighted r hA hB, c, mul_assoc] at he ⊢
  exact he

omit [Fintype κ] [DecidableEq κ] in
theorem rectHSNorm_signedSpectral_sub_intervalIntegrable (r : Nat)
    {A B : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (a b : ℝ) :
    IntervalIntegrable (fun s => rectHSNorm r (cfc (signedSpectralStep s) A - cfc (signedSpectralStep s) B) ^ 2)
      volume a b := by
  simpa only [Matrix.mul_one, Matrix.one_mul] using
    rectHSNorm_signedSpectral_intertwiner_intervalIntegrable r hA hB (1 : Matrix ι ι ℂ) a b

omit [Fintype κ] [DecidableEq κ] in
theorem rectHSNorm_signedSpectral_sub_coarea (r : Nat)
    {A B : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, rectHSNorm r (cfc (signedSpectralStep s) A - cfc (signedSpectralStep s) B) ^ 2) ≤
      2 * rectHSNorm r (1 : Matrix ι ι ℂ) * rectHSNorm r (A - B) := by
  simpa only [Matrix.mul_one, Matrix.one_mul] using
    rectHSNorm_signedSpectral_intertwiner_coarea r hA hB (1 : Matrix ι ι ℂ) a b ha hab

omit [Fintype κ] [DecidableEq κ] in
theorem rectHSNorm_one_sq (r : Nat) :
    rectHSNorm r (1 : Matrix ι ι ℂ) ^ 2 = (Fintype.card ι : ℝ) / r := by
  rw [← matrixTraceReal_gram, Matrix.conjTranspose_one, Matrix.one_mul, matrixTraceReal,
    Matrix.trace_one, Complex.natCast_re]

end ThomGame.Analysis
