module

public import ThomGame.Analysis.MatrixRetainedComplementaryMultiplicity
public import ThomGame.Analysis.MatrixSubalgebraConcreteBlocks
public import ThomGame.Analysis.MatrixSubalgebraBoundedScaleTransport

/-!
# The original algebra scale in the labelled coordinates of its commutant

The reciprocal coefficients of the commutant scale are the scale of
the original algebra in its actual complementary block decomposition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

noncomputable def matrixSubalgebraComplementaryScale : CMatrix d :=
  matrixStarBlockScalar _ R (fun i => (matrixStarRepresentationMultiplicity _ R
    (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype i : ℝ) / R.size i)

theorem matrixSubalgebraComplementaryScale_coefficient_pos (i : Fin R.count) :
    0 < (matrixStarRepresentationMultiplicity _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype i : ℝ) / R.size i :=
  div_pos (Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos _ R _ Subtype.val_injective i))
    (Nat.cast_pos.mpr (R.size_pos i))

theorem matrixSubalgebraComplementaryScale_posDef : (matrixSubalgebraComplementaryScale A R).PosDef :=
  matrixStarBlockScalar_posDef _ R (matrixSubalgebraComplementaryScale_coefficient_pos A R)

theorem matrixSubalgebraComplementaryScale_eq_scale :
    matrixSubalgebraComplementaryScale A R = matrixSubalgebraScale _
      (matrixStarRepresentationRetainedComplementaryBlocks _ R
        (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype) :=
  (matrixStarRepresentationRetainedComplementary_scale _ R
    (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype).symm

variable [NeZero d]

theorem matrixSubalgebraComplementaryScale_mem : matrixSubalgebraComplementaryScale A R ∈ A := by
  apply le_of_eq (matrixSubalgebra_eq_complementary_blocks A R).symm
  rw [matrixSubalgebraComplementaryScale_eq_scale]
  exact matrixSubalgebraScale_mem _ _

theorem matrixSubalgebraComplementaryScale_bounded_norm
    (D : StarSubalgebra ℂ (CMatrix d)) (F : MatrixSubalgebraStarBlocks D) (hDA : D ≤ A)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i) :
    matrixOpNorm (matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s)) ≤ 1 := by
  have hD : D ≤ (matrixStarRepresentationComplementary _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype).range := by
    rw [← matrixSubalgebra_eq_complementary_blocks A R]
    exact hDA
  rw [matrixSubalgebraComplementaryScale_eq_scale, matrixSubalgebraScale]
  exact matrixBoundedScale_inclusion_norm D _ F _ hD _ s (matrixSubalgebraScale_coefficient_pos _ _) hs

end ThomGame.Analysis
