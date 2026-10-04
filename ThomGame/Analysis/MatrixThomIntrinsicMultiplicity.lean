module

public import ThomGame.Analysis.MatrixAlgebraicMultiplicityDistance
public import ThomGame.Analysis.MatrixAlgebraicJointMultiplicity
public import ThomGame.Analysis.MatrixThomExactIntertwiner

/-!
# Thom's quantitative comparison of intrinsic B and A' multiplicities

Use the actual exact B-intertwiner and the actual cut polar factor for
A'. Their rank losses give the original-dimension normalized constants
18 epsilon^2 and 6 epsilon^2. The algebraic factors and all multiplicities
come from actual matrices. A unitary realization of A as the commutant
blocks is not asserted here.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem matrixThom_source_multiplicity_bound (P : MatrixSubalgebraAlgebraicBlocks B)
    (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    matrixAlgebraicMultiplicityDistance B P B.subtype.toAlgHom S.cutSourceRepresentation.toAlgHom /
      d ≤ 18 * ε ^ 2 := by
  obtain ⟨T, hT, _, hr⟩ := S.exists_exact_intertwiner hε0 hBA
  have he := matrixAlgebraicMultiplicityDistance_le_intertwiner B P B.subtype.toAlgHom
    S.cutSourceRepresentation.toAlgHom T (fun X => (hT X).symm)
  have hm := (abs_le.mp S.dimension_error_absolute).2
  apply (div_le_iff₀ (by exact_mod_cast NeZero.pos d : (0 : ℝ) < d)).mpr
  linarith

theorem matrixThom_commutant_multiplicity_bound
    (P : MatrixSubalgebraAlgebraicBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))) :
    matrixAlgebraicMultiplicityDistance _ P
      (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype.toAlgHom
      S.cutCommutantRepresentation.toAlgHom / d ≤ 6 * ε ^ 2 := by
  have he := matrixAlgebraicMultiplicityDistance_le_intertwiner _ P
    (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype.toAlgHom
    S.cutCommutantRepresentation.toAlgHom S.cutPolar (fun X => (S.cutPolar_commutant_intertwines X).symm)
  have hm := (abs_le.mp S.dimension_error_absolute).2
  have hr := S.cutPolar_rank_lower
  apply (div_le_iff₀ (by exact_mod_cast NeZero.pos d : (0 : ℝ) < d)).mpr
  linarith

theorem matrixThom_intrinsic_multiplicity_sum_bound
    (P : MatrixSubalgebraAlgebraicBlocks B)
    (R : MatrixSubalgebraAlgebraicBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    matrixAlgebraicMultiplicityDistance B P B.subtype.toAlgHom S.cutSourceRepresentation.toAlgHom / d +
      matrixAlgebraicMultiplicityDistance _ R
        (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype.toAlgHom
        S.cutCommutantRepresentation.toAlgHom / d ≤ 24 * ε ^ 2 := by
  linarith [matrixThom_source_multiplicity_bound S P hε0 hBA, matrixThom_commutant_multiplicity_bound S R]

theorem exists_matrixThom_intrinsic_multiplicities (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ (P : MatrixSubalgebraAlgebraicBlocks B)
      (R : MatrixSubalgebraAlgebraicBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
      (k : Fin P.count → Fin R.count → Nat),
      (∀ i, matrixAlgebraicRepresentationMultiplicity B P S.cutSourceRepresentation.toAlgHom i =
        ∑ j, R.size j * k i j) ∧
      (∀ j, matrixAlgebraicRepresentationMultiplicity _ R S.cutCommutantRepresentation.toAlgHom j =
        ∑ i, P.size i * k i j) ∧
      S.cut.rank = ∑ i, ∑ j, P.size i * R.size j * k i j ∧
      matrixAlgebraicMultiplicityDistance B P B.subtype.toAlgHom S.cutSourceRepresentation.toAlgHom / d +
        matrixAlgebraicMultiplicityDistance _ R
          (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype.toAlgHom
          S.cutCommutantRepresentation.toAlgHom / d ≤ 24 * ε ^ 2 := by
  obtain ⟨P⟩ := exists_matrixSubalgebraAlgebraicBlocks B
  obtain ⟨R⟩ := exists_matrixSubalgebraAlgebraicBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))
  refine ⟨P, R, matrixAlgebraicJointMultiplicity _ _ P R
    S.cutSourceRepresentation.toAlgHom S.cutCommutantRepresentation.toAlgHom, ?_, ?_, ?_,
    matrixThom_intrinsic_multiplicity_sum_bound S P R hε0 hBA⟩
  · exact matrixAlgebraicJointMultiplicity_row _ _ P R _ _ S.cutRepresentations_commute
  · exact matrixAlgebraicJointMultiplicity_column _ _ P R _ _ S.cutRepresentations_commute
  · exact matrixAlgebraicJointMultiplicity_dimension _ _ P R _ _ S.cutRepresentations_commute

end ThomGame.Analysis
