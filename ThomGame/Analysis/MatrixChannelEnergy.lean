module

public import ThomGame.Analysis.MatrixKrausRepresentation
public import ThomGame.Analysis.MatrixProjectionExclusion
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dirichlet energy of an actual matrix channel

The ambient normalized trace is used throughout. The energy is exactly
half the squared Hilbert norm of the finite Kraus commutator differential.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra BigOperators

variable {d : Nat} [NeZero d]

noncomputable def matrixChannelEnergy (F : CMatrix d →ₗ[ℂ] CMatrix d) (X : CMatrix d) : ℝ :=
  hsNorm X ^ 2 - (normalizedTrace (star X * F X)).re

theorem hsNorm_sub_sq (X Y : CMatrix d) :
    hsNorm (X - Y) ^ 2 = hsNorm X ^ 2 + hsNorm Y ^ 2 -
      2 * (normalizedTrace (star X * Y)).re := by
  have he := norm_sub_sq (𝕜 := ℂ) (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y)
  simp only [← map_sub, finiteMatrixHilbert_norm, finiteMatrixHilbert_inner] at he
  change hsNorm (X - Y) ^ 2 = hsNorm X ^ 2 - 2 * (normalizedTrace (star X * Y)).re + hsNorm Y ^ 2 at he
  linarith

theorem matrixChannelEnergy_kraus {ι : Type*} [Fintype ι]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (a : ι → CMatrix d)
    (hrep : ∀ X, F X = ∑ k, star (a k) * X * a k) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    ∑ k, hsNorm (a k * X - X * a k) ^ 2 = 2 * matrixChannelEnergy F X := by
  have hunit : ∑ k, star (a k) * a k = 1 := by
    simpa only [mul_one] using (hrep 1).symm.trans hF
  have hleft : ∑ k, hsNorm (a k * X) ^ 2 = hsNorm X ^ 2 := by
    have he : ∑ k, normalizedTrace (star (a k * X) * (a k * X)) =
        normalizedTrace (star X * X) := by
      have hg (k : ι) : star (a k * X) * (a k * X) = star X * (star (a k) * a k) * X := by
        simp only [star_mul, mul_assoc]
      simp_rw [hg]
      rw [← normalizedTrace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hunit, mul_one]
    simpa only [Complex.re_sum, normalizedTrace_gram, Complex.ofReal_re] using congrArg Complex.re he
  have hright : ∑ k, hsNorm (X * a k) ^ 2 = hsNorm X ^ 2 := by
    have he := htrace (star X * X)
    rw [hrep] at he
    have he' : ∑ k, normalizedTrace (star (X * a k) * (X * a k)) =
        normalizedTrace (star X * X) := by
      simpa only [normalizedTrace_sum, star_mul, mul_assoc] using he
    simpa only [Complex.re_sum, normalizedTrace_gram, Complex.ofReal_re] using congrArg Complex.re he'
  have hcross : ∑ k, (normalizedTrace (star (a k * X) * (X * a k))).re =
      (normalizedTrace (star X * F X)).re := by
    rw [hrep]
    simp only [star_mul, mul_assoc, Finset.mul_sum, normalizedTrace_sum, Complex.re_sum]
  simp only [hsNorm_sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft, hright, hcross, matrixChannelEnergy]
  ring

noncomputable def matrixKrausDifferential {ι : Type*} [Fintype ι] (a : ι → CMatrix d) :
    CMatrix d →ₗ[ℂ] PiLp 2 (fun _ : ι => FiniteMatrixHilbert d) where
  toFun X := WithLp.toLp 2 (fun k => finiteMatrixHilbertEquiv d (a k * X - X * a k))
  map_add' X Y := by
    apply PiLp.ext
    intro k
    change finiteMatrixHilbertEquiv d _ =
      finiteMatrixHilbertEquiv d (a k * X - X * a k) + finiteMatrixHilbertEquiv d (a k * Y - Y * a k)
    rw [← map_add]
    congr 1
    noncomm_ring
  map_smul' c X := by
    apply PiLp.ext
    intro k
    change finiteMatrixHilbertEquiv d _ = c • finiteMatrixHilbertEquiv d _
    rw [← map_smul]
    congr 1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem matrixKrausDifferential_norm_sq {ι : Type*} [Fintype ι]
    (a : ι → CMatrix d) (X : CMatrix d) :
    ‖matrixKrausDifferential a X‖ ^ 2 = ∑ k, hsNorm (a k * X - X * a k) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun r : ℝ => r ^ 2) (finiteMatrixHilbert_norm d _))

theorem matrixUCP_energy_nonneg (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    0 ≤ matrixChannelEnergy F.toLinearMap X := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus F
  have he := matrixChannelEnergy_kraus F.toLinearMap a ha hF htrace X
  have hn : 0 ≤ ∑ k, hsNorm (a k * X - X * a k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  linarith

theorem matrixUCP_fixed_error_sq_le_energy (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    hsNorm (F X - X) ^ 2 ≤ 2 * matrixChannelEnergy F.toLinearMap X := by
  rw [hsNorm_sub_comm, hsNorm_sub_sq, matrixChannelEnergy]
  have hn := (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mpr
    (matrixUCP_hsNorm_le F hF htrace X)
  change hsNorm X ^ 2 + hsNorm (F X) ^ 2 - 2 * (normalizedTrace (star X * F X)).re ≤
    2 * (hsNorm X ^ 2 - (normalizedTrace (star X * F X)).re)
  linarith

omit [NeZero d] in
theorem matrixChannelEnergy_star (F : CMatrix d →CP CMatrix d) (X : CMatrix d) :
    matrixChannelEnergy F.toLinearMap (star X) = matrixChannelEnergy F.toLinearMap X := by
  have he : (normalizedTrace (X * star (F X))).re =
      (normalizedTrace (star X * F X)).re := by
    rw [normalizedTrace_mul_comm]
    have hh := normalizedTrace_star (star X * F X)
    simpa only [star_mul, star_star, Complex.star_def, Complex.conj_re] using congrArg Complex.re hh
  change hsNorm (star X) ^ 2 - (normalizedTrace (star (star X) * F (star X))).re =
    hsNorm X ^ 2 - (normalizedTrace (star X * F X)).re
  rw [star_star, completelyPositiveMap_star, he, Matrix.star_eq_conjTranspose, hsNorm_conjTranspose]

end ThomGame.Analysis
