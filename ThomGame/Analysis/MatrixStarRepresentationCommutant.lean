module

public import ThomGame.Analysis.MatrixStarRepresentationRealization
public import ThomGame.Analysis.MatrixStandardBlockCommutant
public import ThomGame.Analysis.MatrixCommutantConvexHull
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Concrete commutant blocks for an actual star representation

The same constructed unitary gives coordinates for the representation
and its entire commutant. The latter is the range of the complementary
blocks, even if some simple factors have zero multiplicity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

noncomputable def matrixStarRepresentationCoordinates : CMatrix m ≃⋆ₐ[ℂ]
    Matrix (MatrixStarBlockColumnIndex A P ρ) (MatrixStarBlockColumnIndex A P ρ) ℂ :=
  (Unitary.conjStarAlgAut ℂ (CMatrix m) (matrixStarRepresentationUnitary A P ρ)).symm.trans
    (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)).symm

theorem matrixStarRepresentationCoordinates_apply (T : CMatrix m) :
    matrixStarRepresentationCoordinates A P ρ T =
      Matrix.reindex (matrixStarBlockColumnEquiv A P ρ).symm (matrixStarBlockColumnEquiv A P ρ).symm
        ((matrixStarRepresentationBasis A P ρ)ᴴ * T * matrixStarRepresentationBasis A P ρ) := rfl

theorem matrixStarRepresentationCoordinates_representation (X : A) :
    matrixStarRepresentationCoordinates A P ρ (ρ X) =
      matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X) := by
  change (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)).symm
    ((matrixStarRepresentationBasis A P ρ)ᴴ * ρ X * matrixStarRepresentationBasis A P ρ) = _
  rw [matrixStarRepresentationBasis_conjugates]
  change (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)).symm
    (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)
      (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X))) = _
  exact (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)).symm_apply_apply _

noncomputable def matrixStarRepresentationBlocks :
    ((i : Fin P.count) → CMatrix (P.size i)) →⋆ₐ[ℂ] CMatrix m :=
  (matrixStarRepresentationCoordinates A P ρ).symm.toStarAlgHom.comp
    (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ))

theorem matrixStarRepresentationCoordinates_blocks (X : (i : Fin P.count) → CMatrix (P.size i)) :
    matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationBlocks A P ρ X) =
      matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) X :=
  (matrixStarRepresentationCoordinates A P ρ).apply_symm_apply _

theorem matrixStarRepresentationBlocks_equiv (X : A) :
    matrixStarRepresentationBlocks A P ρ (P.equiv X) = ρ X := by
  apply (matrixStarRepresentationCoordinates A P ρ).injective
  change matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationBlocks A P ρ (P.equiv X)) =
    matrixStarRepresentationCoordinates A P ρ (ρ X)
  rw [matrixStarRepresentationCoordinates_blocks, matrixStarRepresentationCoordinates_representation]

theorem matrixStarRepresentation_range_eq_blocks :
    ρ.range = (matrixStarRepresentationBlocks A P ρ).range := by
  ext T
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨P.equiv X, matrixStarRepresentationBlocks_equiv A P ρ X⟩
  · rintro ⟨X, rfl⟩
    refine ⟨P.equiv.symm X, ?_⟩
    change ρ (P.equiv.symm X) = matrixStarRepresentationBlocks A P ρ X
    simpa only [P.equiv.apply_symm_apply] using (matrixStarRepresentationBlocks_equiv A P ρ (P.equiv.symm X)).symm

noncomputable def matrixStarRepresentationComplementary :
    ((i : Fin P.count) → CMatrix (matrixStarRepresentationMultiplicity A P ρ i)) →⋆ₐ[ℂ] CMatrix m :=
  (matrixStarRepresentationCoordinates A P ρ).symm.toStarAlgHom.comp
    (matrixComplementaryBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ))

theorem matrixStarRepresentationCoordinates_complementary
    (Y : (i : Fin P.count) → CMatrix (matrixStarRepresentationMultiplicity A P ρ i)) :
    matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationComplementary A P ρ Y) =
      matrixComplementaryBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) Y :=
  (matrixStarRepresentationCoordinates A P ρ).apply_symm_apply _

theorem matrixStarRepresentation_mem_commutant_iff (T : CMatrix m) :
    T ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) ↔
      ∃ Y, T = matrixStarRepresentationComplementary A P ρ Y := by
  constructor
  · intro hT
    have hc := (mem_matrixSubalgebraCommutant_iff ρ.range T).mp hT
    have hs : ∀ X, matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) X *
        matrixStarRepresentationCoordinates A P ρ T = matrixStarRepresentationCoordinates A P ρ T *
        matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) X := by
      intro X
      have he := congrArg (matrixStarRepresentationCoordinates A P ρ)
        (hc (ρ (P.equiv.symm X)) ⟨P.equiv.symm X, rfl⟩)
      simpa only [map_mul, matrixStarRepresentationCoordinates_representation, P.equiv.apply_symm_apply] using he
    obtain ⟨Y, hY⟩ := (matrixStandardBlockCommutant_iff P.size (matrixStarRepresentationMultiplicity A P ρ)
      (matrixStarRepresentationCoordinates A P ρ T) P.size_pos).mp hs
    refine ⟨Y, (matrixStarRepresentationCoordinates A P ρ).injective ?_⟩
    change matrixStarRepresentationCoordinates A P ρ T =
      matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationComplementary A P ρ Y)
    rw [matrixStarRepresentationCoordinates_complementary]
    exact hY
  · rintro ⟨Y, rfl⟩
    apply (mem_matrixSubalgebraCommutant_iff ρ.range _).mpr
    rintro _ ⟨X, rfl⟩
    apply (matrixStarRepresentationCoordinates A P ρ).injective
    change matrixStarRepresentationCoordinates A P ρ (ρ X * matrixStarRepresentationComplementary A P ρ Y) =
      matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationComplementary A P ρ Y * ρ X)
    simp only [map_mul, matrixStarRepresentationCoordinates_representation,
      matrixStarRepresentationCoordinates_complementary]
    exact matrixStandard_complementary_blocks_commute _ _ _ _

theorem matrixStarRepresentation_commutant_eq :
    StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) =
      (matrixStarRepresentationComplementary A P ρ).range := by
  ext T
  rw [matrixStarRepresentation_mem_commutant_iff A P ρ]
  exact ⟨fun ⟨Y, hY⟩ => ⟨Y, hY.symm⟩, fun ⟨Y, hY⟩ => ⟨Y, hY.symm⟩⟩

end ThomGame.Analysis
