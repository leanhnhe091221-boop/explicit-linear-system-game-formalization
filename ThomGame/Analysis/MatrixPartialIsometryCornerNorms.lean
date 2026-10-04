module

public import ThomGame.Analysis.MatrixPartialIsometryCorners

/-!
# Operator norms and original traces on partial-isometry corners

Conjugation is contractive on all matrices and isometric on the actual
initial corner. Trace and HS equalities retain an arbitrary denominator r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixRectPartialIsometry_norm_le_one (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) : ‖W‖ ≤ 1 := by
  have he := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hW.nonneg).mpr hW.le_one
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at he
  nlinarith [norm_nonneg W]

theorem matrixPartialIsometry_sandwich_norm_le (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) : ‖W * X * Wᴴ‖ ≤ ‖X‖ := by
  have hw := matrixRectPartialIsometry_norm_le_one W hW
  have hs : ‖Wᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  calc
    _ ≤ ‖W * X‖ * ‖Wᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖W * X‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (norm_nonneg (W * X))
    _ ≤ ‖W‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖X‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg X)

theorem matrixPartialIsometry_sandwich_norm_eq (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d)
    (hL : (Wᴴ * W) * X = X) (hR : X * (Wᴴ * W) = X) : ‖W * X * Wᴴ‖ = ‖X‖ := by
  apply le_antisymm (matrixPartialIsometry_sandwich_norm_le W hW X)
  have hi : IsStarProjection (Wᴴᴴ * Wᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_final_projection hW
  have he := matrixPartialIsometry_sandwich_norm_le Wᴴ hi (W * X * Wᴴ)
  simpa only [Matrix.conjTranspose_conjTranspose, matrixSandwich_inverse_of_support W X hL hR] using he

theorem matrixSandwich_trace_of_support (r : Nat) (W : Matrix (Fin m) (Fin d) ℂ) (X : CMatrix d)
    (hL : (Wᴴ * W) * X = X) : matrixTraceReal r (W * X * Wᴴ) = matrixTraceReal r X := by
  rw [matrixTraceReal_mul_comm r (W * X) Wᴴ, ← Matrix.mul_assoc, hL]

theorem matrixSandwich_hsNorm_of_support (r : Nat) (W : Matrix (Fin m) (Fin d) ℂ) (X : CMatrix d)
    (hL : (Wᴴ * W) * X = X) (hR : X * (Wᴴ * W) = X) :
    rectHSNorm r (W * X * Wᴴ) = rectHSNorm r X := by
  have hLs : (Wᴴ * W) * Xᴴ = Xᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose hR
  have hG : (W * X * Wᴴ)ᴴ * (W * X * Wᴴ) = W * (Xᴴ * X) * Wᴴ := by
    rw [matrixSandwich_star]
    exact matrixSandwich_mul_of_support W Xᴴ X hL
  have hprod : (Wᴴ * W) * (Xᴴ * X) = Xᴴ * X := by rw [← Matrix.mul_assoc, hLs]
  have he : rectHSNorm r (W * X * Wᴴ) ^ 2 = rectHSNorm r X ^ 2 := by
    rw [← matrixTraceReal_gram, hG, matrixSandwich_trace_of_support r W (Xᴴ * X) hprod, matrixTraceReal_gram]
  nlinarith [rectHSNorm_nonneg r (W * X * Wᴴ), rectHSNorm_nonneg r X]

end ThomGame.Analysis
