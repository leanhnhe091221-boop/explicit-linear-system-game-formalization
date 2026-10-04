module

public import ThomGame.Analysis.MatrixThomIntrinsicMultiplicity

/-!
# Vanishing intrinsic multiplicity distance in the original normalization

The block counts and sizes may vary arbitrarily with the coordinate.
The dimension-free bound 24 epsilon^2 implies convergence along any
filter. There is no pointwise small-error restriction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))

theorem matrixThom_intrinsic_multiplicity_tendsto
    (P : (n : ι) → MatrixSubalgebraAlgebraicBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraAlgebraicBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    {L : Filter ι} (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Filter.Tendsto (fun n =>
      matrixAlgebraicMultiplicityDistance (B n) (P n) (B n).subtype.toAlgHom
          (S n).cutSourceRepresentation.toAlgHom / dims n +
        matrixAlgebraicMultiplicityDistance _ (R n)
          (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))).subtype.toAlgHom
          (S n).cutCommutantRepresentation.toAlgHom / dims n) L (𝓝 0) := by
  apply squeeze_zero
    (fun n => add_nonneg
      (div_nonneg (matrixAlgebraicMultiplicityDistance_nonneg _ _ _ _) (Nat.cast_nonneg _))
      (div_nonneg (matrixAlgebraicMultiplicityDistance_nonneg _ _ _ _) (Nat.cast_nonneg _)))
    (fun n => matrixThom_intrinsic_multiplicity_sum_bound (S n) (P n) (R n) (hε0 n) (hBA n))
  simpa using (hε.pow 2).const_mul 24

end ThomGame.Analysis
