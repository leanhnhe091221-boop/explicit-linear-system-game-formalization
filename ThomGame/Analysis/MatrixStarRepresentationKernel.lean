module

public import ThomGame.Analysis.MatrixStarRepresentationCommutant

/-!
# The exact kernel of an actual block representation

Only blocks with positive multiplicity can be detected by the matrix
representation. The criterion is proved from its actual matrix entries.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Nat} (p q : Fin n → Nat)

theorem matrixStandardBlockRepresentation_eq_iff
    (X Y : (i : Fin n) → CMatrix (p i)) :
    matrixStandardBlockRepresentation p q X = matrixStandardBlockRepresentation p q Y ↔
      ∀ i, 0 < q i → X i = Y i := by
  constructor
  · intro h i hi
    ext a b
    have he := congrArg (fun T : Matrix (MatrixStandardBlockIndex p q)
      (MatrixStandardBlockIndex p q) ℂ => T ⟨i, a, ⟨0, hi⟩⟩ ⟨i, b, ⟨0, hi⟩⟩) h
    simpa only [matrixStandardBlockRepresentation_apply_eq, ite_true] using he
  · intro h
    ext ⟨i, a, k⟩ ⟨j, b, l⟩
    by_cases hij : i = j
    · subst j
      rw [matrixStandardBlockRepresentation_apply_eq,
        matrixStandardBlockRepresentation_apply_eq, h i (Nat.zero_lt_of_lt k.isLt)]
    · rw [matrixStandardBlockRepresentation_apply_ne p q X i j hij,
        matrixStandardBlockRepresentation_apply_ne p q Y i j hij]

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

theorem matrixStarRepresentation_eq_iff (X Y : A) :
    ρ X = ρ Y ↔ ∀ i, 0 < matrixStarRepresentationMultiplicity A P ρ i →
      P.equiv X i = P.equiv Y i := by
  rw [← (matrixStarRepresentationCoordinates A P ρ).injective.eq_iff]
  change matrixStarRepresentationCoordinates A P ρ (ρ X) =
    matrixStarRepresentationCoordinates A P ρ (ρ Y) ↔ _
  rw [matrixStarRepresentationCoordinates_representation,
    matrixStarRepresentationCoordinates_representation]
  exact matrixStandardBlockRepresentation_eq_iff _ _ _ _

theorem matrixStarRepresentationBlocks_eq_iff
    (X Y : (i : Fin P.count) → CMatrix (P.size i)) :
    matrixStarRepresentationBlocks A P ρ X = matrixStarRepresentationBlocks A P ρ Y ↔
      ∀ i, 0 < matrixStarRepresentationMultiplicity A P ρ i → X i = Y i := by
  rw [← (matrixStarRepresentationCoordinates A P ρ).injective.eq_iff]
  change matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationBlocks A P ρ X) =
    matrixStarRepresentationCoordinates A P ρ (matrixStarRepresentationBlocks A P ρ Y) ↔ _
  rw [matrixStarRepresentationCoordinates_blocks, matrixStarRepresentationCoordinates_blocks]
  exact matrixStandardBlockRepresentation_eq_iff _ _ _ _

theorem matrixStarRepresentationComplementary_injective :
    Function.Injective (matrixStarRepresentationComplementary A P ρ) := by
  intro X Y h
  have he := congrArg (matrixStarRepresentationCoordinates A P ρ) h
  simp only [matrixStarRepresentationCoordinates_complementary] at he
  change matrixStarReindex (matrixStandardBlockSwap P.size (matrixStarRepresentationMultiplicity A P ρ))
      (matrixStandardBlockRepresentation (matrixStarRepresentationMultiplicity A P ρ) P.size X) =
    matrixStarReindex (matrixStandardBlockSwap P.size (matrixStarRepresentationMultiplicity A P ρ))
      (matrixStandardBlockRepresentation (matrixStarRepresentationMultiplicity A P ρ) P.size Y) at he
  have hs := (matrixStarReindex _).injective he
  funext i
  exact (matrixStandardBlockRepresentation_eq_iff _ _ X Y).mp hs i (P.size_pos i)

theorem matrixStarRepresentationComplementary_eq_iff
    (X Y : (i : Fin P.count) → CMatrix (matrixStarRepresentationMultiplicity A P ρ i)) :
    matrixStarRepresentationComplementary A P ρ X = matrixStarRepresentationComplementary A P ρ Y ↔
      ∀ i, 0 < matrixStarRepresentationMultiplicity A P ρ i → X i = Y i := by
  constructor
  · intro h i _
    exact congrFun (matrixStarRepresentationComplementary_injective A P ρ h) i
  · intro h
    apply congrArg (matrixStarRepresentationComplementary A P ρ)
    funext i
    by_cases hi : 0 < matrixStarRepresentationMultiplicity A P ρ i
    · exact h i hi
    · ext a b
      exact False.elim (hi (Nat.zero_lt_of_lt a.isLt))

end ThomGame.Analysis
