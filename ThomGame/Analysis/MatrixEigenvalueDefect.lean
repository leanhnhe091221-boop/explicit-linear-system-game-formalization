module

public import ThomGame.Analysis.MatrixALTTruncation

/-!
# An eigenvector detects the idempotence defect of its truncation

Self-adjointness moves the defect polynomial to the original eigenvector.
The actual clipped contraction then has a quantitative defect lower bound.
All Hilbert norms and trace pairings use the ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat}

theorem matrix_eigenvector_defect_pairing (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (X : CMatrix d) (lam : ℝ) (heigen : F X = (lam : ℂ) • X) (Y : CMatrix d) :
    normalizedTrace (star X * (F (F Y) - F Y)) =
      ((lam * (lam - 1) : ℝ) : ℂ) * normalizedTrace (star X * Y) := by
  have he (Z : CMatrix d) : normalizedTrace (star X * F Z) =
      (lam : ℂ) * normalizedTrace (star X * Z) := by
    rw [← hpair X Z, heigen, star_smul, Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, normalizedTrace_smul]
  rw [mul_sub, normalizedTrace_sub, he (F Y), he Y]
  push_cast
  ring

theorem matrix_eigenvector_defect_sq [NeZero d] (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (X : CMatrix d) (lam : ℝ) (heigen : F X = (lam : ℂ) • X) (Y : CMatrix d) :
    (lam * (1 - lam)) ^ 2 * (normalizedTrace (star X * Y)).re ^ 2 ≤
      hsNorm X ^ 2 * hsNorm (F (F Y) - F Y) ^ 2 := by
  have hb := pow_le_pow_left₀ (abs_nonneg _)
    (abs_normalizedTrace_pairing_re_le X (F (F Y) - F Y)) 2
  rw [matrix_eigenvector_defect_pairing F hpair X lam heigen Y, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hb
  simpa only [sq_abs, mul_pow, show (lam * (lam - 1)) ^ 2 = (lam * (1 - lam)) ^ 2 by ring] using hb

theorem matrixALTTruncationContraction_pairing [NeZero d]
    (a : ℝ) (ha : 0 < a) (X : CMatrix d)
    (hmoment : a * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    Real.sqrt a / 4 * hsNorm X ^ 2 ≤
      (normalizedTrace (star X * matrixALTTruncationContraction a X)).re := by
  have hb := mul_le_mul_of_nonneg_left (matrixALTTruncation_pairing a ha X hmoment)
    (show 0 ≤ Real.sqrt a / 2 by positivity)
  rw [matrixALTTruncationContraction, mul_smul_comm, normalizedTrace_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  linarith only [hb]

theorem matrixALTTruncationContraction_defect [NeZero d] (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (X : CMatrix d) (hX : X ≠ 0) (lam a : ℝ) (ha : 0 < a)
    (heigen : F X = (lam : ℂ) • X)
    (hmoment : a * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    hsNorm X ^ 2 * lam ^ 2 * (1 - lam) ^ 2 * a / 16 ≤
      hsNorm (F (F (matrixALTTruncationContraction a X)) - F (matrixALTTruncationContraction a X)) ^ 2 := by
  let Y := matrixALTTruncationContraction a X
  have hn : 0 < hsNorm X := lt_of_le_of_ne (hsNorm_nonneg X)
    (Ne.symm (fun h => hX ((hsNorm_eq_zero_iff X).mp h)))
  have hp := matrixALTTruncationContraction_pairing a ha X hmoment
  have hs := pow_le_pow_left₀ (show 0 ≤ Real.sqrt a / 4 * hsNorm X ^ 2 by positivity) hp 2
  have hd := matrix_eigenvector_defect_sq F hpair X lam heigen Y
  have hb : hsNorm X ^ 2 * (hsNorm X ^ 2 * lam ^ 2 * (1 - lam) ^ 2 * a / 16) ≤
      hsNorm X ^ 2 * hsNorm (F (F Y) - F Y) ^ 2 := by
    calc
      _ = (lam * (1 - lam)) ^ 2 * (Real.sqrt a / 4 * hsNorm X ^ 2) ^ 2 := by
        simp only [mul_pow, div_pow, Real.sq_sqrt ha.le]
        ring
      _ ≤ (lam * (1 - lam)) ^ 2 * (normalizedTrace (star X * Y)).re ^ 2 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ ≤ _ := hd
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hb

end ThomGame.Analysis
