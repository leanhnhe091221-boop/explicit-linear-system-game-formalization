module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator bounds for the normalized Hilbert--Schmidt norm

The operator norm is the actual norm on Euclidean-space endomorphisms.
Columnwise estimates prove the dimension-independent inequalities needed
for the two-sided ideal of 2-null bounded matrix sequences.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable def matrixOpNorm {d : Nat} (A : CMatrix d) : ℝ := ‖A‖

variable {d : Nat}

theorem matrixOpNorm_nonneg (A : CMatrix d) : 0 ≤ matrixOpNorm A := norm_nonneg _

@[simp] theorem matrixOpNorm_zero : matrixOpNorm (0 : CMatrix d) = 0 := norm_zero

@[simp] theorem matrixOpNorm_neg (A : CMatrix d) : matrixOpNorm (-A) = matrixOpNorm A := norm_neg _

theorem matrixOpNorm_add_le (A B : CMatrix d) :
    matrixOpNorm (A + B) ≤ matrixOpNorm A + matrixOpNorm B := norm_add_le _ _

theorem matrixOpNorm_mul_le (A B : CMatrix d) :
    matrixOpNorm (A * B) ≤ matrixOpNorm A * matrixOpNorm B := norm_mul_le _ _

@[simp] theorem matrixOpNorm_star (A : CMatrix d) : matrixOpNorm (star A) = matrixOpNorm A :=
  norm_star _

@[simp] theorem matrixOpNorm_smul (c : ℂ) (A : CMatrix d) :
    matrixOpNorm (c • A) = ‖c‖ * matrixOpNorm A := norm_smul _ _

theorem matrixOpNorm_one_le : matrixOpNorm (1 : CMatrix d) ≤ 1 := by
  rcases subsingleton_or_nontrivial (CMatrix d) with h | h
  · have he : (1 : CMatrix d) = 0 := Subsingleton.elim _ _
    rw [he, matrixOpNorm_zero]
    exact zero_le_one
  · exact le_of_eq (norm_one (α := CMatrix d))

theorem matrixOpNorm_unitary_le (U : UnitaryMatrix d) : matrixOpNorm U.val ≤ 1 := by
  have h := CStarRing.norm_coe_unitary_mul U (1 : CMatrix d)
  simpa only [matrixOpNorm, mul_one] using (le_of_eq h).trans matrixOpNorm_one_le

theorem column_square_bound (A B : CMatrix d) (j : Fin d) :
    (∑ i, ‖(A * B) i j‖ ^ 2) ≤ matrixOpNorm A ^ 2 * ∑ i, ‖B i j‖ ^ 2 := by
  let x : EuclideanSpace ℂ (Fin d) := toLp 2 (fun i => B i j)
  have h := A.l2_opNorm_mulVec x
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  have hv : (EuclideanSpace.equiv (Fin d) ℂ).symm (A *ᵥ x.ofLp) =
      (toLp 2 (fun i => (A * B) i j) : EuclideanSpace ℂ (Fin d)) := by
    ext i
    rfl
  rw [hv] at hsq
  have hs : ‖(toLp 2 (fun i => (A * B) i j) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤
      matrixOpNorm A ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow, matrixOpNorm] using hsq
  simpa only [EuclideanSpace.norm_sq_eq, x] using hs

theorem hsNorm_mul_le_left (A B : CMatrix d) :
    hsNorm (A * B) ≤ matrixOpNorm A * hsNorm B := by
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (matrixOpNorm_nonneg _) (hsNorm_nonneg _))).mp
  rw [mul_pow, hsNorm_sq, hsNorm_sq]
  calc
    (∑ i, ∑ j, ‖(A * B) i j‖ ^ 2) / d = (∑ j, ∑ i, ‖(A * B) i j‖ ^ 2) / d := by
      rw [Finset.sum_comm]
    _ ≤ (∑ j, matrixOpNorm A ^ 2 * ∑ i, ‖B i j‖ ^ 2) / d :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => column_square_bound A B j)
        (Nat.cast_nonneg _)
    _ = matrixOpNorm A ^ 2 * ((∑ i, ∑ j, ‖B i j‖ ^ 2) / d) := by
      rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc]

theorem hsNorm_mul_le_right (A B : CMatrix d) :
    hsNorm (A * B) ≤ hsNorm A * matrixOpNorm B := by
  have h := hsNorm_mul_le_left Bᴴ Aᴴ
  simpa only [← conjTranspose_mul, hsNorm_conjTranspose, matrixOpNorm,
    Matrix.l2_opNorm_conjTranspose, mul_comm] using h

theorem hsNorm_le_matrixOpNorm [NeZero d] (A : CMatrix d) : hsNorm A ≤ matrixOpNorm A := by
  simpa only [mul_one, hsNorm_one] using hsNorm_mul_le_left A 1

end ThomGame.Analysis
