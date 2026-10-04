module

public import ThomGame.Analysis.MatrixStarRepresentationRetainedBlocks

/-!
# Positive complementary blocks retain the original multiplicity labels

The central projections in the representation and its commutant agree
in the constructed ambient coordinates. Their ranks determine exactly
the interchanged sizes and multiplicities, also when some blocks vanish.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrixStandard_complementary_support_eq {n : Nat} (p q : Fin n → Nat) (i : Fin n) :
    matrixComplementaryBlockRepresentation p q (Pi.single i 1) =
      matrixStandardBlockRepresentation p q (Pi.single i 1) := by
  classical
  ext ⟨j, a, k⟩ ⟨l, b, t⟩
  by_cases hjl : j = l
  · subst l
    rw [matrixComplementaryBlockRepresentation_apply_eq, matrixStandardBlockRepresentation_apply_eq]
    by_cases hji : j = i
    · subst j
      simp only [Pi.single_eq_same, Matrix.one_apply]
      split_ifs <;> rfl
    · simp only [Pi.single_eq_of_ne hji, Matrix.zero_apply, ite_self]
  · rw [matrixComplementaryBlockRepresentation_apply_ne p q _ j l hjl,
      matrixStandardBlockRepresentation_apply_ne p q _ j l hjl]

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

theorem matrixStarRepresentationComplementary_support (i : Fin P.count) :
    matrixStarRepresentationComplementary A P ρ (Pi.single i 1) =
      ρ (matrixAlgebraicBlockSupport A P.toAlgebraic i) := by
  have he : matrixStarRepresentationComplementary A P ρ (Pi.single i 1) =
      matrixStarRepresentationBlocks A P ρ (Pi.single i 1) := by
    apply (matrixStarRepresentationCoordinates A P ρ).injective
    change matrixStarRepresentationCoordinates A P ρ
        (matrixStarRepresentationComplementary A P ρ (Pi.single i 1)) =
      matrixStarRepresentationCoordinates A P ρ
        (matrixStarRepresentationBlocks A P ρ (Pi.single i 1))
    rw [matrixStarRepresentationCoordinates_complementary, matrixStarRepresentationCoordinates_blocks]
    exact matrixStandard_complementary_support_eq _ _ i
  rw [he, ← matrixAlgebraicBlockInsert_one]
  have h := matrixStarRepresentationBlocks_equiv A P ρ (matrixAlgebraicBlockInsert A P.toAlgebraic i 1)
  change matrixStarRepresentationBlocks A P ρ (P.equiv (P.equiv.symm _)) = _ at h
  simpa only [P.equiv.apply_symm_apply] using h

theorem matrixStarRepresentationRetainedComplementary_support
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count) :
    matrixStarBlockSupport _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ) i =
      ρ (matrixAlgebraicBlockSupport A P.toAlgebraic (matrixStarRepresentationRetainedLabel A P ρ i)) := by
  rw [matrixRetainedBlockRangeBlocks_support, matrixStarRepresentationComplementary_support]

theorem matrixStarRepresentationRetainedComplementary_multiplicity
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count) :
    matrixStarRepresentationMultiplicity _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ)
      (matrixStarRepresentationComplementary A P ρ).range.subtype i =
      P.size (matrixStarRepresentationRetainedLabel A P ρ i) := by
  have hr := matrixStarBlockSupport_rank _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ) i
  rw [matrixStarRepresentationRetainedComplementary_support] at hr
  have hr0 := matrixAlgebraicRepresentation_support_rank A P.toAlgebraic ρ.toAlgHom
    (matrixStarRepresentationRetainedLabel A P ρ i)
  have he : matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) *
      matrixStarRepresentationMultiplicity _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ)
        (matrixStarRepresentationComplementary A P ρ).range.subtype i =
      matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) *
        P.size (matrixStarRepresentationRetainedLabel A P ρ i) := by
    have he0 := (hr0.symm.trans hr).symm
    change matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) *
        matrixStarRepresentationMultiplicity _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ)
          (matrixStarRepresentationComplementary A P ρ).range.subtype i =
      P.size (matrixStarRepresentationRetainedLabel A P ρ i) *
        matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) at he0
    exact he0.trans (Nat.mul_comm _ _)
  exact Nat.eq_of_mul_eq_mul_left (matrixStarRepresentationRetainedLabel_pos A P ρ i) he

theorem matrixStarRepresentationRetainedComplementary_scalar (c : Fin P.count → ℝ) :
    matrixStarBlockScalar _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ)
      (fun i => c (matrixStarRepresentationRetainedLabel A P ρ i)) =
      ρ (matrixStarBlockScalarElement A P c) := by
  rw [← matrixStarRepresentationRetainedBlocks_scalar A P ρ c]
  change (∑ i, (c (matrixStarRepresentationRetainedLabel A P ρ i) : ℂ) •
    matrixStarBlockSupport _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ) i) =
    ∑ i, (c (matrixStarRepresentationRetainedLabel A P ρ i) : ℂ) •
      matrixStarBlockSupport _ (matrixStarRepresentationRetainedBlocks A P ρ) i
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixStarRepresentationRetainedComplementary_support, matrixStarRepresentationRetainedBlocks_support]

theorem matrixStarRepresentationRetainedComplementary_scale :
    matrixSubalgebraScale _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ) =
      ρ (matrixStarBlockScalarElement A P
        (fun i => (matrixStarRepresentationMultiplicity A P ρ i : ℝ) / P.size i)) := by
  rw [matrixSubalgebraScale]
  simp only [matrixStarRepresentationRetainedComplementary_multiplicity]
  simpa only [matrixStarRepresentationRetainedLabel, matrixRetainedBlockLabel] using
    matrixStarRepresentationRetainedComplementary_scalar A P ρ
      (fun i => (matrixStarRepresentationMultiplicity A P ρ i : ℝ) / P.size i)

end ThomGame.Analysis
