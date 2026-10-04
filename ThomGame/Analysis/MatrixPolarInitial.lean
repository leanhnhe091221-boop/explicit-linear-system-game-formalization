module

public import ThomGame.Analysis.MatrixPolarUnitary
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Initial projections under injective changes of range

The polar construction preserves a matrix's right annihilators.
Multiplication on the left by a matrix with a left inverse therefore
preserves its initial projection, including for partial isometries.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem matrixRectAbs_mul_eq_zero {X : Matrix ι κ ℂ} {Z : Matrix κ κ ℂ} (hXZ : X * Z = 0) :
    matrixRectAbs X * Z = 0 := by
  have he := matrix_cfc_intertwine (Matrix.isHermitian_conjTranspose_mul_self X)
    (Matrix.isHermitian_zero (n := κ) (α := ℂ)) Real.sqrt Z (by
      rw [Matrix.mul_assoc, hXZ, Matrix.mul_zero, Matrix.mul_zero])
  rw [matrixRectAbs, matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self X).nonneg]
  simpa only [cfc_apply_zero, Real.sqrt_zero, map_zero, Matrix.mul_zero] using he

omit [DecidableEq ι] in
theorem matrix_absSupport_mul_eq_zero {X : Matrix ι κ ℂ} {Z : Matrix κ κ ℂ} (hXZ : X * Z = 0) :
    matrixRealSupport (matrixRectAbs X) * Z = 0 := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian X)
    (Matrix.isHermitian_zero (n := κ) (α := ℂ))
    (fun t : ℝ => if t = 0 then 0 else 1) Z (by
      rw [matrixRectAbs_mul_eq_zero hXZ, Matrix.mul_zero])
  simpa only [matrixRealSupport, cfc_apply_zero, ite_true, map_zero, Matrix.mul_zero] using he

omit [DecidableEq ι] in
theorem matrix_absSupport_left_factor (B : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) :
    matrixRealSupport (matrixRectAbs (B * X)) * matrixRealSupport (matrixRectAbs X) =
      matrixRealSupport (matrixRectAbs (B * X)) := by
  have hz : (B * X) * (1 - matrixRealSupport (matrixRectAbs X)) = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, matrix_mul_absSupport,
      sub_self, Matrix.mul_zero]
  have he := matrix_absSupport_mul_eq_zero hz
  rw [Matrix.mul_sub, Matrix.mul_one] at he
  exact (sub_eq_zero.mp he).symm

theorem matrix_absSupport_of_left_inverse (B C : Matrix ι ι ℂ) (X : Matrix ι κ ℂ)
    (hCB : C * B = 1) : matrixRealSupport (matrixRectAbs (B * X)) =
      matrixRealSupport (matrixRectAbs X) := by
  have heX : C * (B * X) = X := by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have he := matrix_absSupport_left_factor B X
  have hf := matrix_absSupport_left_factor C (B * X)
  rw [heX] at hf
  have hg := congrArg star hf
  simp only [star_mul, (matrixRealSupport_isStarProjection _).isSelfAdjoint.star_eq] at hg
  exact he.symm.trans hg

theorem matrixRectPolar_initial_of_left_inverse (B C : Matrix ι ι ℂ) (X : Matrix ι κ ℂ)
    (hCB : C * B = 1) : (matrixRectPolar (B * X))ᴴ * matrixRectPolar (B * X) =
      (matrixRectPolar X)ᴴ * matrixRectPolar X := by
  rw [matrixRectPolar_initial, matrixRectPolar_initial, matrix_absSupport_of_left_inverse B C X hCB]

theorem matrixRealSupport_projection {P : Matrix κ κ ℂ} (hP : IsStarProjection P) :
    matrixRealSupport P = P := by
  have hid : cfc (fun t : ℝ => t) P = P := cfc_id ℝ P
  calc
    _ = cfc (fun t : ℝ => t) P := by
      apply cfc_congr
      intro t ht
      have he := hP.isIdempotentElem.spectrum_subset ℝ ht
      rcases he with he | he <;> simp_all
    _ = P := hid

theorem matrixRealInv_projection {P : Matrix κ κ ℂ} (hP : IsStarProjection P) :
    matrixRealInv P = P := by
  have hid : cfc (fun t : ℝ => t) P = P := cfc_id ℝ P
  calc
    _ = cfc (fun t : ℝ => t) P := by
      apply cfc_congr
      intro t ht
      have he := hP.isIdempotentElem.spectrum_subset ℝ ht
      rcases he with he | he <;> simp_all
    _ = P := hid

omit [DecidableEq ι] in
theorem matrixRectAbs_of_initial_projection {X : Matrix ι κ ℂ}
    (hX : IsStarProjection (Xᴴ * X)) : matrixRectAbs X = Xᴴ * X :=
  CFC.sqrt_unique hX.isIdempotentElem.eq hX.nonneg

omit [DecidableEq ι] in
theorem matrixRectPolar_of_initial_projection {X : Matrix ι κ ℂ}
    (hX : IsStarProjection (Xᴴ * X)) : matrixRectPolar X = X := by
  have he := matrix_mul_absSupport X
  rw [matrixRectAbs_of_initial_projection hX, matrixRealSupport_projection hX] at he
  rw [matrixRectPolar, matrixRectAbs_of_initial_projection hX, matrixRealInv_projection hX, he]

theorem matrixRectPolar_initial_partial_isometry_left_inverse (B C : Matrix ι ι ℂ)
    {X : Matrix ι κ ℂ} (hX : IsStarProjection (Xᴴ * X)) (hCB : C * B = 1) :
    (matrixRectPolar (B * X))ᴴ * matrixRectPolar (B * X) = Xᴴ * X := by
  rw [matrixRectPolar_initial_of_left_inverse B C X hCB, matrixRectPolar_of_initial_projection hX]

end ThomGame.Analysis
