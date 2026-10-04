module

public import ThomGame.Analysis.MatrixAnchoredScaleCoordinates
public import ThomGame.Analysis.MatrixThomBoundedScaleStableLimits

/-!
# Thom (4.6) for the actual conditional-median scale and its unitary conjugate

The original scale x is independent of the chosen unitary sequence.
Its pullback is exactly u*xu. Both corrected scales are compared using
the same constructed unitary completion and zero coordinate extensions.
The common stable dimension has ratio one to the original dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDA : ∀ n, D n ≤ A n) (U : (n : ι) → UnitaryMatrix (dims n))
    (hU : ∀ n X, X ∈ D n → (U n).val * X = X * (U n).val)
    (ε : ι → ℝ)
    (S : (n : ι) → MatrixThomSpectralData (A n) (matrixUnitaryPullbackAlgebra (A n) (U n)) (D n) (ε n))

theorem matrixThom_anchoredScale_common_unitary_tendsto
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hBA : ∀ n, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (A n) (U n)) (A n) (ε n)) :
    let P := fun n => matrixUnitaryPullbackBlocks (A n) (U n) (matrixSubalgebraComplementaryBlocks (A n) (R n))
    let hDB := fun n => matrixUnitaryPullback_contains_common (A n) (U n) (D n) (hDA n) (hU n)
    let s := fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n)
    let x := fun n => matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n)
    Tendsto (fun n =>
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame
            (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))) *
              (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame
            ((U n).valᴴ * x n * (U n).val)) +
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame
            (matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))) *
              (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (x n)))
      L (𝓝 0) := by
  dsimp only
  have he := matrixThom_boundedScale_common_unitary_tendsto dims S
    (fun n => matrixUnitaryPullbackBlocks (A n) (U n) (matrixSubalgebraComplementaryBlocks (A n) (R n))) R
    (fun n => matrixUnitaryPullback_contains_common (A n) (U n) (D n) (hDA n) (hU n)) F
    (fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n))
    (fun n => matrixAnchoredScaleCoefficients_pos (D n) (A n) (F n) (R n) (hDA n))
    hDA L hε hε0 hBA
  apply he.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [matrixAnchoredBoundedScale_pullback (D n) (A n) (F n) (R n) (hDA n) (U n) (hU n)]
    rfl)

end ThomGame.Analysis
