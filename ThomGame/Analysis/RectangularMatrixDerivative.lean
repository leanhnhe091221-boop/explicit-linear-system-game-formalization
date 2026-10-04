module

public import ThomGame.Analysis.MatrixResolventDerivative
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Differentiating rectangular matrix products

Finite-dimensional continuous bilinear maps give the product rule
for unrelated row, middle, and column spaces. The adjoint rule is
real-linear, as required by the real tilting parameters.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

noncomputable def rectangularMulCLM :
    Matrix ι κ ℂ →L[ℝ] Matrix κ ν ℂ →L[ℝ] Matrix ι ν ℂ :=
  (_root_.mulLinearMap ℝ).toContinuousBilinearMap

theorem rectangular_mul_hasDerivAt {X : ℝ → Matrix ι κ ℂ} {Y : ℝ → Matrix κ ν ℂ}
    {X' : Matrix ι κ ℂ} {Y' : Matrix κ ν ℂ} {s : ℝ}
    (hX : HasDerivAt X X' s) (hY : HasDerivAt Y Y' s) :
    HasDerivAt (fun a => X a * Y a) (X' * Y s + X s * Y') s := by
  have he := (rectangularMulCLM (ι := ι) (κ := κ) (ν := ν)).hasDerivAt_of_bilinear
    (fun _ => hX) (fun _ => hY)
  simpa only [rectangularMulCLM, LinearMap.toContinuousBilinearMap_apply,
    add_comm] using! he

noncomputable def rectangularAdjointCLM : Matrix ι κ ℂ →L[ℝ] Matrix κ ι ℂ :=
  ({ toFun := Matrix.conjTranspose
     map_add' := Matrix.conjTranspose_add
     map_smul' := fun r X => by simp } : Matrix ι κ ℂ →ₗ[ℝ] Matrix κ ι ℂ).toContinuousLinearMap

theorem rectangular_adjoint_hasDerivAt {X : ℝ → Matrix ι κ ℂ} {X' : Matrix ι κ ℂ} {s : ℝ}
    (hX : HasDerivAt X X' s) : HasDerivAt (fun a => (X a)ᴴ) X'ᴴ s := by
  simpa only [rectangularAdjointCLM, LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def] using!
    (rectangularAdjointCLM (ι := ι) (κ := κ)).hasFDerivAt.comp_hasDerivAt s hX

variable [DecidableEq κ]

theorem squareMatrix_inverse_hasDerivAt {A : ℝ → Matrix κ κ ℂ} {B : Matrix κ κ ℂ} {s : ℝ}
    (hA : HasDerivAt A B s) (hunit : IsUnit (A s)) :
    HasDerivAt (fun a => (A a)⁻¹) (-(A s)⁻¹ * B * (A s)⁻¹) s := by
  obtain ⟨a, ha⟩ := hunit
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) a
  rw [ha] at hi
  have hd := hi.comp_hasDerivAt s hA
  have hai : (↑a⁻¹ : Matrix κ κ ℂ) = Ring.inverse (A s) := by rw [← ha, Ring.inverse_unit]
  simpa only [Matrix.nonsing_inv_eq_ringInverse, neg_apply, Function.comp_def,
    ContinuousLinearMap.mulLeftRight_apply, neg_mul, hai] using! hd

end ThomGame.Analysis
