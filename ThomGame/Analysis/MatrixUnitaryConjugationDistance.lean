module

public import ThomGame.Analysis.MatrixProjectionNearUnitary

/-!
# Uniform change of a contraction under a near-identity unitary

Conjugation changes every operator contraction by at most twice the
distance of the unitary from one, with any original HS denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixUnitary_conjugation_opNorm {m : Nat} (U : UnitaryMatrix m) (X : CMatrix m) :
    matrixOpNorm (U.val * X * U.valᴴ) = matrixOpNorm X := by
  change ‖(U : CMatrix m) * X * (star U : CMatrix m)‖ = ‖X‖
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem matrixUnitary_conjugation_distance {m : Nat} (r : Nat) (U : UnitaryMatrix m)
    (X : CMatrix m) (hX : matrixOpNorm X ≤ 1) :
    rectHSNorm r (X - U.val * X * U.valᴴ) ≤ 2 * rectHSNorm r (U.val - 1) := by
  have he : U.val * X * U.valᴴ - X = (U.val - 1) * X * U.valᴴ + X * (U.valᴴ - 1) := by
    noncomm_ring
  have ha : rectHSNorm r ((U.val - 1) * X * U.valᴴ) ≤ rectHSNorm r (U.val - 1) := by
    change rectHSNorm r (((U.val - 1) * X) * (star U).val) ≤ _
    rw [rectHSNorm_mul_unitary]
    exact (rectHSNorm_mul_le_right r _ X).trans
      (by simpa only [matrixOpNorm, mul_one] using mul_le_mul_of_nonneg_left hX (rectHSNorm_nonneg r _))
  have hs : rectHSNorm r (U.valᴴ - 1) = rectHSNorm r (U.val - 1) := by
    rw [show U.valᴴ - 1 = (U.val - 1)ᴴ by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one], rectHSNorm_conjTranspose]
  have hb : rectHSNorm r (X * (U.valᴴ - 1)) ≤ rectHSNorm r (U.val - 1) := by
    apply (rectHSNorm_mul_le_left r X _).trans
    change matrixOpNorm X * rectHSNorm r (U.valᴴ - 1) ≤ _
    rw [hs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hX (rectHSNorm_nonneg r _)
  rw [rectHSNorm_sub_comm, he]
  have ht := (rectHSNorm_add_le r ((U.val - 1) * X * U.valᴴ) (X * (U.valᴴ - 1))).trans
    (add_le_add ha hb)
  simpa only [two_mul] using ht

end ThomGame.Analysis
