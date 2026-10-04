module

public import ThomGame.Analysis.RectangularMatrixDerivative
public import ThomGame.Analysis.RectangularHilbertSchmidt
public import Mathlib.Analysis.Matrix.Order

/-!
# Real traces with an explicit original normalization

The trace on an auxiliary space is divided by the dimension of the
original space, as is the rectangular Hilbert--Schmidt norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def matrixTraceReal (r : Nat) (A : Matrix ι ι ℂ) : ℝ := A.trace.re / r

@[simp] theorem matrixTraceReal_zero (r : Nat) : matrixTraceReal r (0 : Matrix ι ι ℂ) = 0 := by
  simp [matrixTraceReal]

@[simp] theorem matrixTraceReal_add (r : Nat) (A B : Matrix ι ι ℂ) :
    matrixTraceReal r (A + B) = matrixTraceReal r A + matrixTraceReal r B := by
  simp [matrixTraceReal, add_div]

@[simp] theorem matrixTraceReal_sub (r : Nat) (A B : Matrix ι ι ℂ) :
    matrixTraceReal r (A - B) = matrixTraceReal r A - matrixTraceReal r B := by
  simp [matrixTraceReal, sub_div]

@[simp] theorem matrixTraceReal_sum {μ : Type*} (r : Nat) (s : Finset μ) (A : μ → Matrix ι ι ℂ) :
    matrixTraceReal r (∑ i ∈ s, A i) = ∑ i ∈ s, matrixTraceReal r (A i) := by
  simp [matrixTraceReal, Finset.sum_div]

@[simp] theorem matrixTraceReal_real_smul (r : Nat) (c : ℝ) (A : Matrix ι ι ℂ) :
    matrixTraceReal r (c • A) = c * matrixTraceReal r A := by
  simp [matrixTraceReal, mul_div_assoc]

theorem matrixTraceReal_mul_comm (r : Nat) (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    matrixTraceReal r (A * B) = matrixTraceReal r (B * A) := by
  simp only [matrixTraceReal, Matrix.trace_mul_comm A B]

theorem matrixTraceReal_gram (r : Nat) (X : Matrix ι κ ℂ) :
    matrixTraceReal r (Xᴴ * X) = rectHSNorm r X ^ 2 := by
  rw [matrixTraceReal, rectangular_trace_gram, Complex.ofReal_re, rectHSNorm_sq]

theorem matrixTraceReal_nonneg [DecidableEq ι] (r : Nat) {A : Matrix ι ι ℂ} (hA : 0 ≤ A) :
    0 ≤ matrixTraceReal r A := by
  apply div_nonneg _ (Nat.cast_nonneg r)
  exact (Complex.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg).1

theorem matrixTraceReal_mono [DecidableEq ι] (r : Nat) {A B : Matrix ι ι ℂ} (hAB : A ≤ B) :
    matrixTraceReal r A ≤ matrixTraceReal r B := by
  have he := matrixTraceReal_nonneg r (sub_nonneg.mpr hAB)
  rw [matrixTraceReal_sub] at he
  linarith

noncomputable def matrixTraceRealCLM (r : Nat) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  ({ toFun := matrixTraceReal r
     map_add' := matrixTraceReal_add r
     map_smul' := fun c A => matrixTraceReal_real_smul r c A } :
    Matrix ι ι ℂ →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem matrixTraceReal_hasDerivAt (r : Nat) {A : ℝ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ} {s : ℝ}
    (hA : HasDerivAt A B s) : HasDerivAt (fun a => matrixTraceReal r (A a)) (matrixTraceReal r B) s := by
  simpa only [matrixTraceRealCLM, LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def] using!
    (matrixTraceRealCLM (ι := ι) r).hasFDerivAt.comp_hasDerivAt s hA

end ThomGame.Analysis
