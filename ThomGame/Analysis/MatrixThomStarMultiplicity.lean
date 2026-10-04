module

public import ThomGame.Analysis.MatrixSubalgebraConcreteBlocks
public import ThomGame.Analysis.MatrixThomIntrinsicMultiplicity

/-!
# Thom's actual star blocks and the quantitative formula (3.3)

The same star block choices describe B and its corrected image, and
describe A and its correction through the complementary blocks of A'.
The joint table consists of ranks of actual products of matrix units.
The weighted distance uses the original dimension d throughout.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

theorem matrixThom_star_block_algebras :
    B = (matrixStarRepresentationBlocks B P B.subtype).range ∧
    S.correctedSourceAlgebra = (matrixStarRepresentationBlocks B P S.cutSourceRepresentation).range ∧
    A = (matrixStarRepresentationComplementary _ R
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype).range ∧
    S.correctedTargetAlgebra = (matrixStarRepresentationComplementary _ R S.cutCommutantRepresentation).range :=
  ⟨matrixSubalgebra_eq_standard_blocks B P,
    matrixStarRepresentation_range_eq_blocks B P S.cutSourceRepresentation,
    matrixSubalgebra_eq_complementary_blocks A R,
    matrixStarRepresentation_commutant_eq _ R S.cutCommutantRepresentation⟩

theorem matrixThom_star_multiplicity_bound (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    (∑ j, (R.size j : ℝ) * |(matrixStarRepresentationMultiplicity _ R S.cutCommutantRepresentation j : ℝ) -
      (matrixStarRepresentationMultiplicity _ R
        (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype j : ℝ)|) / d +
    (∑ i, (P.size i : ℝ) * |(matrixStarRepresentationMultiplicity B P S.cutSourceRepresentation i : ℝ) -
      (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ)|) / d ≤ 24 * ε ^ 2 := by
  rw [add_comm]
  exact matrixThom_intrinsic_multiplicity_sum_bound S P.toAlgebraic R.toAlgebraic hε0 hBA

theorem exists_matrixThom_star_multiplicities (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ (P : MatrixSubalgebraStarBlocks B)
      (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
      (k : Fin P.count → Fin R.count → Nat),
      (∀ i, matrixStarRepresentationMultiplicity B P S.cutSourceRepresentation i = ∑ j, R.size j * k i j) ∧
      (∀ j, matrixStarRepresentationMultiplicity _ R S.cutCommutantRepresentation j = ∑ i, P.size i * k i j) ∧
      S.cut.rank = ∑ i, ∑ j, P.size i * R.size j * k i j ∧
      B = (matrixStarRepresentationBlocks B P B.subtype).range ∧
      S.correctedSourceAlgebra = (matrixStarRepresentationBlocks B P S.cutSourceRepresentation).range ∧
      A = (matrixStarRepresentationComplementary _ R
        (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype).range ∧
      S.correctedTargetAlgebra = (matrixStarRepresentationComplementary _ R S.cutCommutantRepresentation).range ∧
      (∑ j, (R.size j : ℝ) * |(matrixStarRepresentationMultiplicity _ R S.cutCommutantRepresentation j : ℝ) -
        (matrixStarRepresentationMultiplicity _ R
          (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype j : ℝ)|) / d +
      (∑ i, (P.size i : ℝ) * |(matrixStarRepresentationMultiplicity B P S.cutSourceRepresentation i : ℝ) -
        (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ)|) / d ≤ 24 * ε ^ 2 := by
  obtain ⟨Q⟩ := exists_matrixSubalgebraStarBlocks B
  obtain ⟨T⟩ := exists_matrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))
  obtain ⟨hB, hB', hA, hA'⟩ := matrixThom_star_block_algebras S Q T
  refine ⟨Q, T, matrixAlgebraicJointMultiplicity _ _ Q.toAlgebraic T.toAlgebraic
    S.cutSourceRepresentation.toAlgHom S.cutCommutantRepresentation.toAlgHom,
    ?_, ?_, ?_, hB, hB', hA, hA', matrixThom_star_multiplicity_bound S Q T hε0 hBA⟩
  · exact matrixAlgebraicJointMultiplicity_row _ _ Q.toAlgebraic T.toAlgebraic _ _ S.cutRepresentations_commute
  · exact matrixAlgebraicJointMultiplicity_column _ _ Q.toAlgebraic T.toAlgebraic _ _ S.cutRepresentations_commute
  · exact matrixAlgebraicJointMultiplicity_dimension _ _ Q.toAlgebraic T.toAlgebraic _ _ S.cutRepresentations_commute

end ThomGame.Analysis
