module

public import ThomGame.Analysis.MatrixInverseSqrtCommutator

/-!
# Product and adjoint bounds for unitary commutators

These bounds use the actual operator and normalized Hilbert--Schmidt
norms. In particular, a contraction X has boundary energy controlling
that of XX* with the factor four after squaring.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem hsNorm_commutator_mul_le (U A B : CMatrix d) :
    hsNorm (U * (A * B) - (A * B) * U) ≤
      hsNorm (U * A - A * U) * matrixOpNorm B + matrixOpNorm A * hsNorm (U * B - B * U) := by
  have he : U * (A * B) - (A * B) * U = (U * A - A * U) * B + A * (U * B - B * U) := by noncomm_ring
  rw [he]
  exact (hsNorm_add_le _ _).trans (add_le_add (hsNorm_mul_le_right _ _) (hsNorm_mul_le_left _ _))

theorem hsNorm_unitary_commutator_star (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (U.val * star X - star X * U.val) = hsNorm (U.val * X - X * U.val) := by
  have he : hsNorm (star (star U.val * X - X * star U.val)) =
      hsNorm (star U.val * X - X * star U.val) := hsNorm_conjTranspose _
  simp only [star_sub, star_mul, star_star] at he
  rw [hsNorm_sub_comm (star X * U.val)] at he
  exact he.trans (hsNorm_unitary_star_commutator U X)

theorem hsNorm_unitary_commutator_gram_le (U : UnitaryMatrix d) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) :
    hsNorm (U.val * (X * star X) - (X * star X) * U.val) ≤ 2 * hsNorm (U.val * X - X * U.val) := by
  have he := hsNorm_commutator_mul_le U.val X (star X)
  rw [matrixOpNorm_star, hsNorm_unitary_commutator_star] at he
  have hn := mul_le_mul_of_nonneg_left hX (hsNorm_nonneg (U.val * X - X * U.val))
  nlinarith

theorem matrixProjectionResolventFactor_norm_le {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : IsStarProjection F) :
    matrixOpNorm (matrixProjectionResolventFactor lam S F) ≤ 1 := by
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (matrixProjectionResolventDifference_nonneg hlam hS hF)).mpr
      (matrixProjectionResolventDifference_le_one hlam hS hF)
  rw [matrixProjectionResolventDifference_eq_factor hlam hS hF, CStarRing.norm_self_mul_star] at hn
  change ‖matrixProjectionResolventFactor lam S F‖ ≤ 1
  nlinarith [norm_nonneg (matrixProjectionResolventFactor lam S F)]

end ThomGame.Analysis
