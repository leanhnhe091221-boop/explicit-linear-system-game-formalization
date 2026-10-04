module

public import ThomGame.Analysis.MatrixUCPTraceBounds

/-!
# Pairings of nearby completions of orthogonal matrices

Full complex trace pairings are controlled by the original normalized
Hilbert norm. Orthogonality is a genuine zero complex pairing.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem norm_normalizedTrace_pairing_le (X Y : CMatrix d) :
    ‖normalizedTrace (star X * Y)‖ ≤ hsNorm X * hsNorm Y := by
  simpa only [finiteMatrixHilbert_inner, finiteMatrixHilbert_norm] using
    norm_inner_le_norm (𝕜 := ℂ) (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y)

theorem matrixOrthogonal_perturbed_pairing (X Y U V : CMatrix d)
    (horth : normalizedTrace (star X * Y) = 0) :
    ‖normalizedTrace (star U * V)‖ ≤ hsNorm (U - X) * hsNorm V + hsNorm X * hsNorm (V - Y) := by
  have he : normalizedTrace (star U * V) = normalizedTrace (star (U - X) * V) +
      normalizedTrace (star X * (V - Y)) := by
    simp only [star_sub, sub_mul, mul_sub, normalizedTrace_sub, horth, sub_zero]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_normalizedTrace_pairing_le _ _)
    (norm_normalizedTrace_pairing_le _ _))

theorem matrixOrthogonal_close_pairing_sq (X Y U V : CMatrix d) (rho M : ℝ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M) (horth : normalizedTrace (star X * Y) = 0)
    (hX : hsNorm X ^ 2 ≤ M) (hV : hsNorm V ^ 2 ≤ M)
    (hUX : hsNorm (U - X) ^ 2 ≤ 4 * rho * M) (hVY : hsNorm (V - Y) ^ 2 ≤ 4 * rho * M) :
    ‖normalizedTrace (star U * V)‖ ^ 2 ≤ 16 * rho * M ^ 2 := by
  have he := matrixOrthogonal_perturbed_pairing X Y U V horth
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg
    (mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))
    (mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)))).mpr he
  have hfirst := mul_le_mul hUX hV (sq_nonneg (hsNorm V)) (by positivity : 0 ≤ 4 * rho * M)
  have hsecond := mul_le_mul hX hVY (sq_nonneg (hsNorm (V - Y))) hM
  nlinarith [sq_nonneg (hsNorm (U - X) * hsNorm V - hsNorm X * hsNorm (V - Y))]

end ThomGame.Analysis
