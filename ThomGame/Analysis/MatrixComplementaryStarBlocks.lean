module

public import ThomGame.Analysis.MatrixStarBlocksTransport
public import ThomGame.Analysis.MatrixSubalgebraComplementaryScale

/-!
# Complementary blocks on the original algebra itself

The equality with the constructed complementary range transports its
actual star blocks to A without changing any ambient matrix or trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable def matrixStarSubalgebraEquivOfEq {d : Nat}
    (A B : StarSubalgebra ℂ (CMatrix d)) (h : A = B) : A ≃⋆ₐ[ℂ] B := by
  subst B
  exact StarAlgEquiv.refl ℂ A

theorem matrixStarSubalgebraEquivOfEq_coe {d : Nat}
    (A B : StarSubalgebra ℂ (CMatrix d)) (h : A = B) (X : A) :
    (matrixStarSubalgebraEquivOfEq A B h X : CMatrix d) = X := by
  subst B
  rfl

variable {d : Nat} [NeZero d] (A : StarSubalgebra ℂ (CMatrix d))
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

noncomputable abbrev matrixSubalgebraComplementaryBlocks : MatrixSubalgebraStarBlocks A :=
  matrixStarBlocksTransport _ A
    (matrixStarRepresentationRetainedComplementaryBlocks _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype)
    (matrixStarSubalgebraEquivOfEq A _ (matrixSubalgebra_eq_complementary_blocks A R))

theorem matrixSubalgebraComplementaryBlocks_scale :
    matrixSubalgebraScale A (matrixSubalgebraComplementaryBlocks A R) = matrixSubalgebraComplementaryScale A R := by
  have h := matrixStarBlocksTransport_scale _ A
    (matrixStarRepresentationRetainedComplementaryBlocks _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype)
    (matrixStarSubalgebraEquivOfEq A _ (matrixSubalgebra_eq_complementary_blocks A R))
    (fun X => by rw [matrixStarSubalgebraEquivOfEq_coe])
  rw [matrixStarSubalgebraEquivOfEq_coe] at h
  exact h.trans (matrixSubalgebraComplementaryScale_eq_scale A R).symm

end ThomGame.Analysis
