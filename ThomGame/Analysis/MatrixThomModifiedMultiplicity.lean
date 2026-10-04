module

public import ThomGame.Analysis.MatrixThomIntrinsicMultiplicityLimits
public import ThomGame.Analysis.MatrixThomModifiedData

/-!
# Intrinsic multiplicity estimates for the same general correction data

Construct blocks of the modified B and A' on the original index set and
use the very same spectral data as the general tracial correction. The
normalization remains the original dimension at every coordinate.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
    (A B : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)

structure MatrixThomModifiedMultiplicityBlocks where
  source : (i : ι) → MatrixSubalgebraAlgebraicBlocks (matrixSmallErrorAlgebra dims B ε i)
  commutant : (i : ι) → MatrixSubalgebraAlgebraicBlocks
    (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i))))

theorem exists_matrixThomModifiedMultiplicityBlocks :
    Nonempty (MatrixThomModifiedMultiplicityBlocks dims A B ε) :=
  ⟨⟨fun i => Classical.choice (exists_matrixSubalgebraAlgebraicBlocks (matrixSmallErrorAlgebra dims B ε i)),
    fun i => Classical.choice (exists_matrixSubalgebraAlgebraicBlocks
      (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i)))))⟩⟩

variable [∀ i, NeZero (dims i)] {A B ε}
    {D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))}
    (S : MatrixThomModifiedData dims A B D ε)
    (P : MatrixThomModifiedMultiplicityBlocks dims A B ε)

noncomputable def matrixThomModifiedMultiplicityDistance (i : ι) : ℝ :=
  matrixAlgebraicMultiplicityDistance _ (P.source i)
      (matrixSmallErrorAlgebra dims B ε i).subtype.toAlgHom (S i).cutSourceRepresentation.toAlgHom / dims i +
    matrixAlgebraicMultiplicityDistance _ (P.commutant i)
      (StarSubalgebra.centralizer ℂ (matrixSmallErrorAlgebra dims A ε i : Set (CMatrix (dims i)))).subtype.toAlgHom
      (S i).cutCommutantRepresentation.toAlgHom / dims i

theorem matrixThomModifiedMultiplicityDistance_nonneg (i : ι) :
    0 ≤ matrixThomModifiedMultiplicityDistance dims S P i :=
  add_nonneg
    (div_nonneg (matrixAlgebraicMultiplicityDistance_nonneg _ _ _ _) (Nat.cast_nonneg _))
    (div_nonneg (matrixAlgebraicMultiplicityDistance_nonneg _ _ _ _) (Nat.cast_nonneg _))

theorem matrixThomModifiedMultiplicityDistance_bound
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) (i : ι) :
    matrixThomModifiedMultiplicityDistance dims S P i ≤ 24 * (matrixSmallError ε i) ^ 2 :=
  matrixThom_intrinsic_multiplicity_sum_bound (S i) (P.source i) (P.commutant i)
    (matrixSmallError_nonneg ε hε0 i) (matrixSmallError_nearInclusion dims A B ε hBA i)

theorem matrixThomModifiedMultiplicityDistance_tendsto
    (L : Filter ι) (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    Filter.Tendsto (matrixThomModifiedMultiplicityDistance dims S P) L (𝓝 0) :=
  matrixThom_intrinsic_multiplicity_tendsto dims S P.source P.commutant
    (matrixSmallError_tendsto ε L hε) (matrixSmallError_nonneg ε hε0)
    (matrixSmallError_nearInclusion dims A B ε hBA)

end ThomGame.Analysis
