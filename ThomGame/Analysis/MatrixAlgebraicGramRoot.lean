module

public import ThomGame.Analysis.MatrixAlgebraicGramIntertwining
public import ThomGame.Analysis.MatrixSubalgebraPolar

/-!
# The positive Gram square root and its inverse inside the original algebra

Finite-dimensional closedness and functional calculus construct both
elements in the actual star subalgebra. Invertibility is proved from the
positive definite Gram matrix; it is not an extra assumption.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

noncomputable def matrixAlgebraicGramRoot : A :=
  ⟨CFC.sqrt (matrixAlgebraicGram A S : CMatrix d), by
    let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
    rw [matrixSqrt_eq_real_cfc (matrixAlgebraicGram_posDef A S).posSemidef.nonneg]
    exact cfc_mem (𝕜' := ℂ) (s := A) Real.sqrt (matrixAlgebraicGram A S).property⟩

theorem matrixAlgebraicGramRoot_val :
    (matrixAlgebraicGramRoot A S : CMatrix d) = CFC.sqrt (matrixAlgebraicGram A S : CMatrix d) := rfl

theorem matrixAlgebraicGramRoot_star : star (matrixAlgebraicGramRoot A S) = matrixAlgebraicGramRoot A S := by
  apply Subtype.ext
  exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (matrixAlgebraicGram A S : CMatrix d))).star_eq

theorem matrixAlgebraicGramRoot_mul_self :
    matrixAlgebraicGramRoot A S * matrixAlgebraicGramRoot A S = matrixAlgebraicGram A S := by
  apply Subtype.ext
  exact CFC.sqrt_mul_sqrt_self _ (matrixAlgebraicGram_posDef A S).posSemidef.nonneg

theorem matrixAlgebraicGramRoot_isUnit : IsUnit (matrixAlgebraicGramRoot A S : CMatrix d) := by
  apply isUnit_mul_self_iff.mp
  have he := congrArg Subtype.val (matrixAlgebraicGramRoot_mul_self A S)
  change (matrixAlgebraicGramRoot A S : CMatrix d) * (matrixAlgebraicGramRoot A S : CMatrix d) =
    (matrixAlgebraicGram A S : CMatrix d) at he
  rw [he]
  exact matrixAlgebraicGram_isUnit A S

theorem matrixAlgebraicGramRoot_support :
    matrixRealSupport (matrixAlgebraicGramRoot A S : CMatrix d) = 1 := by
  apply (matrixAlgebraicGramRoot_isUnit A S).mul_right_cancel
  rw [matrixRealSupport_mul (IsSelfAdjoint.isHermitian
    (show IsSelfAdjoint (matrixAlgebraicGramRoot A S : CMatrix d) from
      congrArg Subtype.val (matrixAlgebraicGramRoot_star A S))), one_mul]

noncomputable def matrixAlgebraicGramRootInv : A :=
  ⟨matrixRealInv (matrixAlgebraicGramRoot A S : CMatrix d), by
    let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
    exact cfc_mem (𝕜' := ℂ) (s := A) (fun t : ℝ => t⁻¹) (matrixAlgebraicGramRoot A S).property⟩

theorem matrixAlgebraicGramRootInv_star :
    star (matrixAlgebraicGramRootInv A S) = matrixAlgebraicGramRootInv A S := by
  apply Subtype.ext
  exact (matrixRealInv_isSelfAdjoint _).star_eq

theorem matrixAlgebraicGramRoot_inv_mul :
    matrixAlgebraicGramRootInv A S * matrixAlgebraicGramRoot A S = 1 := by
  apply Subtype.ext
  change matrixRealInv (matrixAlgebraicGramRoot A S : CMatrix d) *
    (matrixAlgebraicGramRoot A S : CMatrix d) = 1
  rw [matrixRealInv_mul (IsSelfAdjoint.isHermitian
    (show IsSelfAdjoint (matrixAlgebraicGramRoot A S : CMatrix d) from
      congrArg Subtype.val (matrixAlgebraicGramRoot_star A S))), matrixAlgebraicGramRoot_support]

theorem matrixAlgebraicGramRoot_mul_inv :
    matrixAlgebraicGramRoot A S * matrixAlgebraicGramRootInv A S = 1 := by
  have he := congrArg star (matrixAlgebraicGramRoot_inv_mul A S)
  simpa only [star_mul, matrixAlgebraicGramRoot_star, matrixAlgebraicGramRootInv_star, star_one] using he

noncomputable def matrixAlgebraicGramRootUnit : Aˣ where
  val := matrixAlgebraicGramRoot A S
  inv := matrixAlgebraicGramRootInv A S
  val_inv := matrixAlgebraicGramRoot_mul_inv A S
  inv_val := matrixAlgebraicGramRoot_inv_mul A S

end ThomGame.Analysis
