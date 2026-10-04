module

public import ThomGame.Analysis.MatrixThomStarMultiplicity
public import ThomGame.Analysis.MatrixThomIntrinsicMultiplicityLimits

/-!
# Formula (3.3) for the actual star blocks

The source factors and complementary target factors are those already
identified with the actual original and corrected subalgebras. Their
weighted multiplicity distance tends to zero in the original dimensions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))

theorem matrixThom_star_multiplicity_tendsto
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    {L : Filter ι} (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Filter.Tendsto (fun n =>
      (∑ j, ((R n).size j : ℝ) * |(matrixStarRepresentationMultiplicity _ (R n) (S n).cutCommutantRepresentation j : ℝ) -
        (matrixStarRepresentationMultiplicity _ (R n)
          (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))).subtype j : ℝ)|) / dims n +
      (∑ i, ((P n).size i : ℝ) * |(matrixStarRepresentationMultiplicity (B n) (P n) (S n).cutSourceRepresentation i : ℝ) -
        (matrixStarRepresentationMultiplicity (B n) (P n) (B n).subtype i : ℝ)|) / dims n) L (𝓝 0) := by
  have h := matrixThom_intrinsic_multiplicity_tendsto dims S (fun n => (P n).toAlgebraic)
    (fun n => (R n).toAlgebraic) hε hε0 hBA
  exact h.congr' (Filter.Eventually.of_forall (fun n => add_comm _ _))

end ThomGame.Analysis
