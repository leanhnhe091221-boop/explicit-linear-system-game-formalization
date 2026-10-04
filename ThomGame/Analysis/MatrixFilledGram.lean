module

public import ThomGame.Analysis.MatrixExponentialTilt

/-!
# Filling the kernel of a rectangular Gram matrix

Adding the complementary initial support to X*X gives an actual
invertible matrix. Its inverse is the squared spectral inverse of
|X| plus that same complementary projection.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem matrix_support_fill_inverse {A : Matrix κ κ ℂ} (hA : Matrix.IsHermitian A) :
    (A * A + (1 - matrixRealSupport A)) *
      (matrixRealInv A * matrixRealInv A + (1 - matrixRealSupport A)) = 1 := by
  have hfill : cfc (fun s : ℝ => s * s + (1 - if s = 0 then 0 else 1)) A =
      A * A + (1 - matrixRealSupport A) := by
    rw [cfc_add A _ _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA.isSelfAdjoint]
    have hid : cfc (fun s : ℝ => s) A = A := cfc_id ℝ A
    rw [hid]
    rfl
  have hinv : cfc (fun s : ℝ => s⁻¹ * s⁻¹ + (1 - if s = 0 then 0 else 1)) A =
      matrixRealInv A * matrixRealInv A + (1 - matrixRealSupport A) := by
    rw [cfc_add A _ _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA.isSelfAdjoint]
    rfl
  rw [← hfill, ← hinv, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) A := by
      apply cfc_congr
      intro s _
      dsimp only
      by_cases hs : s = 0
      · simp [hs]
      · simp only [hs, ite_false, sub_self, add_zero]
        field_simp
    _ = 1 := cfc_const_one ℝ A hA.isSelfAdjoint

noncomputable def matrixFilledGram (X : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  Xᴴ * X + (1 - matrixRealSupport (matrixRectAbs X))

noncomputable def matrixFilledGramInv (X : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  matrixRealInv (matrixRectAbs X) * matrixRealInv (matrixRectAbs X) +
    (1 - matrixRealSupport (matrixRectAbs X))

theorem matrixFilledGram_mul_inv (X : Matrix ι κ ℂ) :
    matrixFilledGram X * matrixFilledGramInv X = 1 := by
  simpa only [matrixFilledGram, matrixFilledGramInv, matrixRectAbs_mul_self] using
    matrix_support_fill_inverse (matrixRectAbs_isHermitian X)

theorem matrixFilledGram_isHermitian (X : Matrix ι κ ℂ) :
    Matrix.IsHermitian (matrixFilledGram X) :=
  (Matrix.isHermitian_conjTranspose_mul_self X).add
    (matrixRealSupport_isStarProjection _).one_sub.isSelfAdjoint.isHermitian

theorem matrixFilledGramInv_isHermitian (X : Matrix ι κ ℂ) :
    Matrix.IsHermitian (matrixFilledGramInv X) := by
  show (matrixFilledGramInv X)ᴴ = matrixFilledGramInv X
  simp only [matrixFilledGramInv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    (matrixRealInv_isSelfAdjoint _).isHermitian.eq,
    (matrixRealSupport_isStarProjection (matrixRectAbs X)).one_sub.isSelfAdjoint.isHermitian.eq]

theorem matrixFilledGram_inv_mul (X : Matrix ι κ ℂ) :
    matrixFilledGramInv X * matrixFilledGram X = 1 := by
  have he := congrArg Matrix.conjTranspose (matrixFilledGram_mul_inv X)
  simpa only [Matrix.conjTranspose_mul, (matrixFilledGram_isHermitian X).eq,
    (matrixFilledGramInv_isHermitian X).eq, Matrix.conjTranspose_one] using he

theorem matrixFilledGram_isUnit (X : Matrix ι κ ℂ) : IsUnit (matrixFilledGram X) :=
  ⟨⟨matrixFilledGram X, matrixFilledGramInv X, matrixFilledGram_mul_inv X,
    matrixFilledGram_inv_mul X⟩, rfl⟩

theorem matrixFilledGram_inverse (X : Matrix ι κ ℂ) :
    (matrixFilledGram X)⁻¹ = matrixFilledGramInv X :=
  Matrix.inv_eq_right_inv (matrixFilledGram_mul_inv X)

theorem matrixFilledGram_range_formula (X : Matrix ι κ ℂ) :
    X * (matrixFilledGram X)⁻¹ * Xᴴ = matrixRectPolar X * (matrixRectPolar X)ᴴ := by
  have hz : X * (1 - matrixRealSupport (matrixRectAbs X)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, matrix_mul_absSupport, sub_self]
  rw [matrixFilledGram_inverse, matrixFilledGramInv, Matrix.mul_add, hz, add_zero,
    matrixRectPolar, Matrix.conjTranspose_mul, (matrixRealInv_isSelfAdjoint _).isHermitian.eq]
  simp only [Matrix.mul_assoc]

end ThomGame.Analysis
