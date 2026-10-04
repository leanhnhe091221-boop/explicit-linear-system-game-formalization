module

public import ThomGame.Analysis.MatrixThomAnchoredStableTransport
public import ThomGame.Analysis.MatrixThomBoundedScaleOrder
public import ThomGame.Analysis.MatrixThomOrderedTransport

/-!
# Actual conditional medians asymptotically commute with the given unitary

The finite order and equal original traces eliminate drift under the
already constructed common transport. The conclusion uses the original
matrix dimension, and no commutation or concentration limit is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDA : ∀ n, D n ≤ A n) (U : (n : ι) → UnitaryMatrix (dims n))
    (hU : ∀ n X, X ∈ D n → (U n).val * X = X * (U n).val)
    (ε : ι → ℝ)
    (S : (n : ι) → MatrixThomSpectralData (A n) (matrixUnitaryPullbackAlgebra (A n) (U n)) (D n) (ε n))

include hU S in
theorem matrixThom_anchoredScale_conjugation_tendsto
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hBA : ∀ n, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (A n) (U n)) (A n) (ε n)) :
    Tendsto (fun n => hsNorm
      ((U n).valᴴ * matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) * (U n).val -
        matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n))) L (𝓝 0) := by
  let P := fun n => matrixUnitaryPullbackBlocks (A n) (U n) (matrixSubalgebraComplementaryBlocks (A n) (R n))
  let hDB := fun n => matrixUnitaryPullback_contains_common (A n) (U n) (D n) (hDA n) (hU n)
  let s := fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n)
  let x := fun n => matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n)
  have hs n : ∀ i, 0 < s n i := matrixAnchoredScaleCoefficients_pos (D n) (A n) (F n) (R n) (hDA n)
  have horder n := matrixThom_boundedScale_order (S n) (P n) (R n) (hDB n) (F n) (s n) (hs n)
  refine matrixThom_ordered_transport_tendsto dims S (fun n => (U n).valᴴ * x n * (U n).val) x
    (fun n => matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))
    (fun n => matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))
    (fun n => (horder n).1.posSemidef.nonneg) (fun n => (horder n).2.1)
    (fun n => sub_nonneg.mp (horder n).2.2.posSemidef.nonneg) ?_ L hε ?_
  · intro n
    have hunit : (U n).val * (U n).valᴴ = 1 := (U n).prop.2
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · exact matrixThom_anchoredScale_common_unitary_tendsto dims A D F R hDA U hU ε S L hε hε0 hBA

include hU S in
theorem matrixThom_anchoredScale_commutator_tendsto
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hBA : ∀ n, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (A n) (U n)) (A n) (ε n)) :
    Tendsto (fun n => hsNorm
      (matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) * (U n).val -
        (U n).val * matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n))) L (𝓝 0) := by
  apply (matrixThom_anchoredScale_conjugation_tendsto dims A D F R hDA U hU ε S L hε hε0 hBA).congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    have hunit : (U n).val * (U n).valᴴ = 1 := (U n).prop.2
    have he (X : CMatrix (dims n)) :
        (U n).val * ((U n).valᴴ * X * (U n).val - X) = X * (U n).val - (U n).val * X := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hunit, one_mul]
    rw [← he, ← rectHSNorm_eq_hsNorm, ← rectHSNorm_eq_hsNorm, rectHSNorm_unitary_mul]

end ThomGame.Analysis
