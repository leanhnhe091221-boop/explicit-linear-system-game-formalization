module

public import ThomGame.Analysis.MatrixStarRepresentationKernel
public import ThomGame.Analysis.MatrixRetainedBlockUnits
public import ThomGame.Analysis.MatrixSubalgebraScale

/-!
# Actual positive blocks of a representation and its commutant

Zero multiplicities are discarded by their original labels. Both
retained decompositions use the same constructed matrix coordinates.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

noncomputable abbrev matrixStarRepresentationRetainedLabel :=
  matrixRetainedBlockLabel (fun i => 0 < matrixStarRepresentationMultiplicity A P ρ i)

noncomputable abbrev matrixStarRepresentationRetainedBlocks :
    MatrixSubalgebraStarBlocks (matrixStarRepresentationBlocks A P ρ).range :=
  matrixRetainedBlockRangeBlocks P.size (fun i => 0 < matrixStarRepresentationMultiplicity A P ρ i)
    (matrixStarRepresentationBlocks A P ρ) (matrixStarRepresentationBlocks_eq_iff A P ρ)
    (fun i _ => P.size_pos i)

noncomputable abbrev matrixStarRepresentationRetainedComplementaryBlocks :
    MatrixSubalgebraStarBlocks (matrixStarRepresentationComplementary A P ρ).range :=
  matrixRetainedBlockRangeBlocks (matrixStarRepresentationMultiplicity A P ρ)
    (fun i => 0 < matrixStarRepresentationMultiplicity A P ρ i)
    (matrixStarRepresentationComplementary A P ρ) (matrixStarRepresentationComplementary_eq_iff A P ρ)
    (fun _ h => h)

theorem matrixStarRepresentationRetainedLabel_pos
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count) :
    0 < matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) := by
  change Fin (Fintype.card {i : Fin P.count // 0 < matrixStarRepresentationMultiplicity A P ρ i}) at i
  exact matrixRetainedBlockLabel_mem (fun j : Fin P.count => 0 < matrixStarRepresentationMultiplicity A P ρ j) i

theorem matrixStarRepresentationRetainedBlocks_unit
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count)
    (a b : Fin (P.size (matrixStarRepresentationRetainedLabel A P ρ i))) :
    (matrixStarBlockUnit _ (matrixStarRepresentationRetainedBlocks A P ρ) i a b : CMatrix m) =
      ρ (matrixStarBlockUnit A P (matrixStarRepresentationRetainedLabel A P ρ i) a b) := by
  rw [matrixRetainedBlockRangeBlocks_unit]
  have h := matrixStarRepresentationBlocks_equiv A P ρ
    (matrixStarBlockUnit A P (matrixStarRepresentationRetainedLabel A P ρ i) a b)
  change matrixStarRepresentationBlocks A P ρ (P.equiv (P.equiv.symm _)) = _ at h
  simpa only [P.equiv.apply_symm_apply] using h

theorem matrixStarRepresentationRetainedBlocks_multiplicity
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count) :
    matrixStarRepresentationMultiplicity _ (matrixStarRepresentationRetainedBlocks A P ρ)
      (matrixStarRepresentationBlocks A P ρ).range.subtype i =
      matrixStarRepresentationMultiplicity A P ρ (matrixStarRepresentationRetainedLabel A P ρ i) := by
  change (matrixStarBlockUnit _ (matrixStarRepresentationRetainedBlocks A P ρ) i
    ⟨0, _⟩ ⟨0, _⟩ : CMatrix m).rank = _
  rw [matrixStarRepresentationRetainedBlocks_unit]
  rfl

theorem matrixStarRepresentationRetainedBlocks_support
    (i : Fin (matrixStarRepresentationRetainedBlocks A P ρ).count) :
    matrixStarBlockSupport _ (matrixStarRepresentationRetainedBlocks A P ρ) i =
      ρ (matrixAlgebraicBlockSupport A P.toAlgebraic (matrixStarRepresentationRetainedLabel A P ρ i)) := by
  rw [matrixRetainedBlockRangeBlocks_support]
  have h := matrixStarRepresentationBlocks_equiv A P ρ
    (matrixAlgebraicBlockInsert A P.toAlgebraic (matrixStarRepresentationRetainedLabel A P ρ i) 1)
  change matrixStarRepresentationBlocks A P ρ (P.equiv (P.equiv.symm _)) = _ at h
  have he := congrArg ρ (matrixAlgebraicBlockInsert_one A P.toAlgebraic
    (matrixStarRepresentationRetainedLabel A P ρ i))
  simp only [P.equiv.apply_symm_apply] at h
  exact h.trans he

theorem matrixStarRepresentationRetainedBlocks_scalar (c : Fin P.count → ℝ) :
    matrixStarBlockScalar _ (matrixStarRepresentationRetainedBlocks A P ρ)
      (fun i => c (matrixStarRepresentationRetainedLabel A P ρ i)) =
      ρ (matrixStarBlockScalarElement A P c) := by
  rw [matrixRetainedBlockRangeBlocks_scalar]
  have he : (fun i => (c i : ℂ) • (1 : CMatrix (P.size i))) =
      P.equiv (matrixStarBlockScalarElement A P c) := by
    funext i
    exact (matrixStarBlockScalarElement_equiv A P c i).symm
  rw [he, matrixStarRepresentationBlocks_equiv]

theorem matrixStarRepresentationRetainedBlocks_scale :
    matrixSubalgebraScale _ (matrixStarRepresentationRetainedBlocks A P ρ) =
      ρ (matrixStarBlockScalarElement A P
        (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P ρ i)) := by
  rw [matrixSubalgebraScale]
  simp only [matrixStarRepresentationRetainedBlocks_multiplicity]
  simpa only [matrixStarRepresentationRetainedLabel, matrixRetainedBlockLabel] using
    matrixStarRepresentationRetainedBlocks_scalar A P ρ
      (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P ρ i)

end ThomGame.Analysis
