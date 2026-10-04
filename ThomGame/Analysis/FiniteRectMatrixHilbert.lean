module

public import ThomGame.Analysis.RectangularHilbertSchmidt
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# A rectangular matrix Hilbert space with the original normalization

The denominator r is independent of both matrix dimensions. The type
alias separates the trace Hilbert norm from matrix operator norms.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

def FiniteRectMatrixHilbert (_r m d : Nat) := Matrix (Fin m) (Fin d) ℂ

variable (r m d : Nat)

instance finiteRectMatrixHilbertAddCommGroup : AddCommGroup (FiniteRectMatrixHilbert r m d) :=
  inferInstanceAs (AddCommGroup (Matrix (Fin m) (Fin d) ℂ))

instance finiteRectMatrixHilbertModule : Module ℂ (FiniteRectMatrixHilbert r m d) :=
  inferInstanceAs (Module ℂ (Matrix (Fin m) (Fin d) ℂ))

def finiteRectMatrixHilbertEquiv : Matrix (Fin m) (Fin d) ℂ ≃ₗ[ℂ] FiniteRectMatrixHilbert r m d :=
  LinearEquiv.refl ℂ _

instance finiteRectMatrixHilbertFiniteDimensional : FiniteDimensional ℂ (FiniteRectMatrixHilbert r m d) :=
  FiniteDimensional.of_injective (finiteRectMatrixHilbertEquiv r m d).symm.toLinearMap
    (finiteRectMatrixHilbertEquiv r m d).symm.injective

theorem rectangular_normalized_trace_gram (X : Matrix (Fin m) (Fin d) ℂ) :
    (Xᴴ * X).trace / (r : ℂ) = (rectHSNorm r X ^ 2 : ℝ) := by
  rw [rectangular_trace_gram, rectHSNorm_sq]
  push_cast
  rfl

variable [NeZero r]

@[instance_reducible] noncomputable def finiteRectMatrixHilbertInnerCore :
    InnerProductSpace.Core ℂ (FiniteRectMatrixHilbert r m d) where
  inner x y := (((finiteRectMatrixHilbertEquiv r m d).symm x)ᴴ *
    (finiteRectMatrixHilbertEquiv r m d).symm y).trace / (r : ℂ)
  conj_inner_symm x y := by
    change star (_ : ℂ) = _
    rw [star_div₀, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, star_natCast]
  re_inner_nonneg x := by
    rw [rectangular_normalized_trace_gram, RCLike.re_to_complex, Complex.ofReal_re]
    exact sq_nonneg _
  add_left x y z := by
    rw [map_add, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, add_div]
  smul_left x y c := by
    rw [map_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul]
    simp only [smul_eq_mul, mul_div_assoc]
    rfl
  definite x hx := by
    apply (finiteRectMatrixHilbertEquiv r m d).symm.injective
    rw [rectangular_normalized_trace_gram, Complex.ofReal_eq_zero] at hx
    exact (rectHSNorm_eq_zero_iff (NeZero.pos r) _).mp (sq_eq_zero_iff.mp hx)

noncomputable instance finiteRectMatrixHilbertNormedAddCommGroup :
    NormedAddCommGroup (FiniteRectMatrixHilbert r m d) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := finiteRectMatrixHilbertInnerCore r m d)

noncomputable instance finiteRectMatrixHilbertInnerProductSpace :
    InnerProductSpace ℂ (FiniteRectMatrixHilbert r m d) :=
  letI := finiteRectMatrixHilbertInnerCore r m d
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (FiniteRectMatrixHilbert r m d))

theorem finiteRectMatrixHilbert_inner (X Y : Matrix (Fin m) (Fin d) ℂ) :
    inner ℂ (finiteRectMatrixHilbertEquiv r m d X) (finiteRectMatrixHilbertEquiv r m d Y) =
      (Xᴴ * Y).trace / (r : ℂ) := rfl

theorem finiteRectMatrixHilbert_norm (X : Matrix (Fin m) (Fin d) ℂ) :
    ‖finiteRectMatrixHilbertEquiv r m d X‖ = rectHSNorm r X := by
  change Real.sqrt ((Xᴴ * X).trace / (r : ℂ)).re = rectHSNorm r X
  rw [rectangular_normalized_trace_gram, Complex.ofReal_re,
    Real.sqrt_sq (rectHSNorm_nonneg r X)]

end ThomGame.Analysis
