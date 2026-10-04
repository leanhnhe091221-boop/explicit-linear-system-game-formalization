module

public import ThomGame.Analysis.MatrixChannelEnergySeminorm

/-!
# The product estimate ALT (5.7)

The Leibniz identity for the actual Kraus differential, together with the
two operator-norm module bounds, controls products of contractions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra BigOperators

variable {d : Nat} [NeZero d]

theorem matrixKrausDifferential_mul_le {ι : Type*} [Fintype ι]
    (a : ι → CMatrix d) (X Y : CMatrix d) (hX : matrixOpNorm X ≤ 1) (hY : matrixOpNorm Y ≤ 1) :
    ‖matrixKrausDifferential a (X * Y)‖ ≤ ‖matrixKrausDifferential a X‖ + ‖matrixKrausDifferential a Y‖ := by
  let L : PiLp 2 (fun _ : ι => FiniteMatrixHilbert d) :=
    WithLp.toLp 2 (fun k => finiteMatrixHilbertEquiv d ((a k * X - X * a k) * Y))
  let R : PiLp 2 (fun _ : ι => FiniteMatrixHilbert d) :=
    WithLp.toLp 2 (fun k => finiteMatrixHilbertEquiv d (X * (a k * Y - Y * a k)))
  have he : matrixKrausDifferential a (X * Y) = L + R := by
    apply PiLp.ext
    intro k
    change finiteMatrixHilbertEquiv d _ = finiteMatrixHilbertEquiv d _ + finiteMatrixHilbertEquiv d _
    rw [← map_add]
    congr 1
    noncomm_ring
  have hL : ‖L‖ ≤ ‖matrixKrausDifferential a X‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, matrixKrausDifferential_norm_sq]
    apply Finset.sum_le_sum
    intro k _
    change ‖finiteMatrixHilbertEquiv d _‖ ^ 2 ≤ _
    rw [finiteMatrixHilbert_norm]
    apply (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mpr
    exact (hsNorm_mul_le_right _ Y).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hY (hsNorm_nonneg (a k * X - X * a k)))
  have hR : ‖R‖ ≤ ‖matrixKrausDifferential a Y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, matrixKrausDifferential_norm_sq]
    apply Finset.sum_le_sum
    intro k _
    change ‖finiteMatrixHilbertEquiv d _‖ ^ 2 ≤ _
    rw [finiteMatrixHilbert_norm]
    apply (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mpr
    exact (hsNorm_mul_le_left X _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hX (hsNorm_nonneg (a k * Y - Y * a k)))
  rw [he]
  exact (norm_add_le L R).trans (add_le_add hL hR)

theorem matrixUCP_energy_sqrt_mul_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (X Y : CMatrix d) (hX : matrixOpNorm X ≤ 1) (hY : matrixOpNorm Y ≤ 1) :
    Real.sqrt (matrixChannelEnergy F.toLinearMap (X * Y)) ≤
      Real.sqrt (matrixChannelEnergy F.toLinearMap X) + Real.sqrt (matrixChannelEnergy F.toLinearMap Y) := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus F
  have hn := matrixKrausDifferential_norm_eq F.toLinearMap a ha hF htrace
  have he := matrixKrausDifferential_mul_le a X Y hX hY
  rw [hn, hn, hn, ← mul_add] at he
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp he

theorem matrixUCP_fixed_error_le_sqrt_energy (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    hsNorm (F X - X) ≤ Real.sqrt 2 * Real.sqrt (matrixChannelEnergy F.toLinearMap X) := by
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (matrixUCP_energy_nonneg F hF htrace X)]
  exact matrixUCP_fixed_error_sq_le_energy F hF htrace X

theorem matrixUCP_product_fixed_error (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (X Y : CMatrix d) (hX : matrixOpNorm X ≤ 1) (hY : matrixOpNorm Y ≤ 1) :
    hsNorm (F (X * Y) - X * Y) ≤ Real.sqrt 2 *
      (Real.sqrt (matrixChannelEnergy F.toLinearMap X) + Real.sqrt (matrixChannelEnergy F.toLinearMap Y)) :=
  (matrixUCP_fixed_error_le_sqrt_energy F hF htrace (X * Y)).trans
    (mul_le_mul_of_nonneg_left (matrixUCP_energy_sqrt_mul_le F hF htrace X Y hX hY) (Real.sqrt_nonneg _))

end ThomGame.Analysis
