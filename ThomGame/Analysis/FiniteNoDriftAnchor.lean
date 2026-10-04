module

public import ThomGame.Analysis.FiniteNoDriftBounds
public import ThomGame.Analysis.MatrixAnchoredScaleCoordinates

/-! A finite Poincare anchor concentrates the actual conditional median. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (A D : StarSubalgebra ℂ (CMatrix d))
    (F : MatrixSubalgebraStarBlocks D)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDA : D ≤ A)

theorem finiteNoDrift_anchored_transport
    (U : UnitaryMatrix d) (hU : ∀ X ∈ D, U.val * X = X * U.val)
    {ε : ℝ} (S : MatrixThomSpectralData A (matrixUnitaryPullbackAlgebra A U) D ε)
    (hε : 0 ≤ ε) (hBA : MatrixNearInclusion (matrixUnitaryPullbackAlgebra A U) A ε) :
    let P := matrixUnitaryPullbackBlocks A U (matrixSubalgebraComplementaryBlocks A R)
    let hDB := matrixUnitaryPullback_contains_common A U D hDA hU
    let s := matrixAnchoredScaleCoefficients D A F R hDA
    let x := matrixAnchoredBoundedScale D A F R hDA
    rectHSNorm d (matrixFrameLift S.stableSourceFrame (U.valᴴ * x * U.val) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s))) ≤ 17 * ε ∧
    rectHSNorm d (matrixFrameLift S.stableSourceFrame x -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))) ≤ 9 * ε := by
  dsimp only
  constructor
  · have hb := S.finite_sourceBoundedScale_bound
      (matrixUnitaryPullbackBlocks A U (matrixSubalgebraComplementaryBlocks A R))
      (matrixUnitaryPullback_contains_common A U D hDA hU) F
      (matrixAnchoredScaleCoefficients D A F R hDA)
      (matrixAnchoredScaleCoefficients_pos D A F R hDA) hε hBA
    rw [matrixAnchoredBoundedScale_pullback D A F R hDA U hU] at hb
    exact hb
  · exact S.finite_targetBoundedScale_bound R
      (matrixUnitaryPullback_contains_common A U D hDA hU) F
      (matrixAnchoredScaleCoefficients D A F R hDA)
      (matrixAnchoredScaleCoefficients_pos D A F R hDA) hDA hε

theorem finiteNoDrift_anchored_commutator
    (U : UnitaryMatrix d) (hU : ∀ X ∈ D, U.val * X = X * U.val)
    {ε : ℝ} (S : MatrixThomSpectralData A (matrixUnitaryPullbackAlgebra A U) D ε)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hBA : MatrixNearInclusion (matrixUnitaryPullbackAlgebra A U) A ε) :
    hsNorm (matrixAnchoredBoundedScale D A F R hDA * U.val -
      U.val * matrixAnchoredBoundedScale D A F R hDA) ≤
        2 * (26 * ε + Real.sqrt (26 * ε)) := by
  let P := matrixUnitaryPullbackBlocks A U (matrixSubalgebraComplementaryBlocks A R)
  let hDB := matrixUnitaryPullback_contains_common A U D hDA hU
  let s := matrixAnchoredScaleCoefficients D A F R hDA
  let x := matrixAnchoredBoundedScale D A F R hDA
  have hs : ∀ i, 0 < s i := matrixAnchoredScaleCoefficients_pos D A F R hDA
  have horder := matrixThom_boundedScale_order S P R hDB F s hs
  have ht := finiteNoDrift_anchored_transport A D F R hDA U hU S hε hBA
  have hunit : U.val * U.valᴴ = 1 := U.prop.2
  have hb := S.finite_ordered_transport (U.valᴴ * x * U.val) x
    (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s))
    (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))
    horder.1.posSemidef.nonneg horder.2.1 (sub_nonneg.mp horder.2.2.posSemidef.nonneg)
    (by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hunit, Matrix.one_mul])
    hε hsmall (show _ ≤ 26 * ε by linarith [ht.1, ht.2])
  have he : U.val * (U.valᴴ * x * U.val - x) = x * U.val - U.val * x := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, hunit, one_mul]
  change hsNorm (x * U.val - U.val * x) ≤ _
  rw [← he, ← rectHSNorm_eq_hsNorm, rectHSNorm_unitary_mul, rectHSNorm_eq_hsNorm]
  exact hb

/-- A uniform commutator-bound formulation avoids a choice of a maximizing generator. -/
def FiniteNoDriftAnchor {h : Nat} (U : Fin h → UnitaryMatrix d) (K ν : ℝ) : Prop :=
  ∀ X : CMatrix d, X ∈ A → IsSelfAdjoint X → matrixOpNorm X ≤ 1 →
    ∀ r : ℝ, (∀ j, hsNorm (X * (U j).val - (U j).val * X) ≤ r) →
      hsNorm (X - matrixTraceProjection D X) ≤ K * r + ν

theorem finiteNoDrift_anchored_concentration
    {h : Nat} (U : Fin h → UnitaryMatrix d)
    (hU : ∀ j X, X ∈ D → (U j).val * X = X * (U j).val)
    {ε K ν : ℝ}
    (S : (j : Fin h) → MatrixThomSpectralData A (matrixUnitaryPullbackAlgebra A (U j)) D ε)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hBA : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (U j)) A ε)
    (hanchor : FiniteNoDriftAnchor A D U K ν) :
    hsNorm (matrixAnchoredBoundedScale D A F R hDA - (1 / 2 : ℂ) • 1) ≤
      K * (2 * (26 * ε + Real.sqrt (26 * ε))) + ν := by
  have hspec := matrixAnchoredBoundedScale_spec D A F R hDA
  have hb := hanchor (matrixAnchoredBoundedScale D A F R hDA) hspec.2.2.1
    hspec.1.posSemidef.isHermitian.isSelfAdjoint hspec.2.2.2 _
    (fun j => finiteNoDrift_anchored_commutator A D F R hDA (U j) (hU j)
      (S j) hε hsmall (hBA j))
  rwa [matrixAnchoredBoundedScale_expectation D A F R hDA] at hb

end ThomGame.Analysis
