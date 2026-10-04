module

public import ThomGame.Analysis.MatrixThomStarMultiplicityLimits
public import ThomGame.Analysis.MatrixThomModifiedMultiplicity

/-!
# Actual star blocks for the same general relative correction

Choose star blocks on the original index set. Their underlying algebraic
blocks use the previously defined distance for exactly the same spectral
data S. On a filter-large set their concrete ranges equal the original
A and B; corrected ranges are identified at every coordinate.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
    (A B : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)

structure MatrixThomModifiedStarBlocks where
  source : (i : ι) → MatrixSubalgebraStarBlocks (matrixSmallErrorAlgebra dims B ε i)
  commutant : (i : ι) → MatrixSubalgebraStarBlocks
    (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i))))

theorem exists_matrixThomModifiedStarBlocks : Nonempty (MatrixThomModifiedStarBlocks dims A B ε) :=
  ⟨⟨fun i => Classical.choice (exists_matrixSubalgebraStarBlocks (matrixSmallErrorAlgebra dims B ε i)),
    fun i => Classical.choice (exists_matrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i)))))⟩⟩

noncomputable abbrev MatrixThomModifiedStarBlocks.toAlgebraic (P : MatrixThomModifiedStarBlocks dims A B ε) :
    MatrixThomModifiedMultiplicityBlocks dims A B ε :=
  ⟨fun i => (P.source i).toAlgebraic, fun i => (P.commutant i).toAlgebraic⟩

variable [∀ i, NeZero (dims i)] {A B ε}
    {D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))}
    (S : MatrixThomModifiedData dims A B D ε)
    (P : MatrixThomModifiedStarBlocks dims A B ε)

theorem matrixThomModifiedStar_corrected_algebras (i : ι) :
    (S i).correctedSourceAlgebra =
      (matrixStarRepresentationBlocks _ (P.source i) (S i).cutSourceRepresentation).range ∧
    (S i).correctedTargetAlgebra =
      (matrixStarRepresentationComplementary _ (P.commutant i) (S i).cutCommutantRepresentation).range :=
  ⟨matrixStarRepresentation_range_eq_blocks _ (P.source i) (S i).cutSourceRepresentation,
    matrixStarRepresentation_commutant_eq _ (P.commutant i) (S i).cutCommutantRepresentation⟩

theorem matrixThomModifiedStar_original_algebras_eventually
    (L : Filter ι) (hε : Filter.Tendsto ε L (𝓝 0)) :
    ∀ᶠ i in L,
      B i = (matrixStarRepresentationBlocks _ (P.source i) (matrixSmallErrorAlgebra dims B ε i).subtype).range ∧
      A i = (matrixStarRepresentationComplementary _ (P.commutant i)
        (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i)))).subtype).range := by
  filter_upwards [matrixSmallErrorAlgebra_eventually_eq dims A ε L hε,
    matrixSmallErrorAlgebra_eventually_eq dims B ε L hε] with i hA hB
  exact ⟨hB.symm.trans (matrixSubalgebra_eq_standard_blocks _ (P.source i)),
    hA.symm.trans (matrixSubalgebra_eq_complementary_blocks _ (P.commutant i))⟩

theorem matrixThomModifiedStar_multiplicity_tendsto
    (L : Filter ι) (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    Filter.Tendsto (matrixThomModifiedMultiplicityDistance dims S (P.toAlgebraic dims A B ε)) L (𝓝 0) :=
  matrixThomModifiedMultiplicityDistance_tendsto dims S (P.toAlgebraic dims A B ε) L hε hε0 hBA

end ThomGame.Analysis
