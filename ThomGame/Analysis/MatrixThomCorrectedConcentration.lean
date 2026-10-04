module

public import ThomGame.Analysis.MatrixAnchoredScaleSequence
public import ThomGame.Analysis.MatrixThomAnchoredStableTransport
public import ThomGame.Analysis.MatrixThomScalarTransport
public import ThomGame.Analysis.MatrixThomScaleConcentration

/-!
# Concentration of both actual corrected scales

Original concentration and the same common transport force both retained
scales to concentrate in the corrected normalization. Zero-dimensional
exceptional coordinates are allowed; positivity is proved eventually.
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

theorem matrixThom_correctedScale_concentration
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hBA : ∀ n, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (A n) (U n)) (A n) (ε n))
    (hX : Tendsto (fun n => hsNorm (matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) -
      (1 / 2 : ℂ) • 1)) L (𝓝 0)) :
    let P := fun n => matrixUnitaryPullbackBlocks (A n) (U n) (matrixSubalgebraComplementaryBlocks (A n) (R n))
    let hDB := fun n => matrixUnitaryPullback_contains_common (A n) (U n) (D n) (hDA n) (hU n)
    let s := fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n)
    Tendsto (fun n => (S n).retainedScaleConcentration (P n) (R n) (hDB n) (F n) (s n)) L (𝓝 0) := by
  dsimp only
  let P := fun n => matrixUnitaryPullbackBlocks (A n) (U n) (matrixSubalgebraComplementaryBlocks (A n) (R n))
  let hDB := fun n => matrixUnitaryPullback_contains_common (A n) (U n) (D n) (hDA n) (hU n)
  let s := fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n)
  let M := fun n => (S n).commonPositiveScalar (hDB n) (F n) (s n)
  let ym := fun n => matrixBoundedScale ((S n).retainedSourceScale (P n)) (M n)
  let yp := fun n => matrixBoundedScale ((S n).retainedTargetScale (R n)) (M n)
  have hnorm n : matrixOpNorm (ym n) ≤ 1 ∧ matrixOpNorm (yp n) ≤ 1 := by
    have hM := (S n).commonPositiveScalar_posDef (hDB n) (F n) (s n)
      (matrixAnchoredScaleCoefficients_pos (D n) (A n) (F n) (R n) (hDA n))
    have hmem := (S n).commonPositiveScalar_mem_retainedSource (P n) (hDB n) (F n) (s n)
    exact ⟨matrixBoundedScale_norm_le_one ((S n).retainedSourceScale_posDef (P n)) hM
        (matrixSubalgebraScale_commutes _ _ _ hmem),
      matrixBoundedScale_norm_le_one ((S n).retainedTargetScale_posDef (R n)) hM
        (matrixSubalgebraScale_commutes _ _ _ ((S n).retainedRange_le (P n) (R n) hmem))⟩
  let Ym : BoundedMatrixSequence (fun n => (S n).cut.rank) := ⟨ym, 1, zero_le_one, fun n => (hnorm n).1⟩
  let Yp : BoundedMatrixSequence (fun n => (S n).cut.rank) := ⟨yp, 1, zero_le_one, fun n => (hnorm n).2⟩
  let X := matrixAnchoredScaleSequence dims A D F R hDA
  let V := boundedUnitarySequence dims U
  let Xm := star V * X * V
  let em := fun n => rectHSNorm (S n).stableDim
    (matrixFrameLift (S n).stableTargetFrame (Ym.val n) * (S n).stableUnitary.val -
      (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (Xm.val n))
  let ep := fun n => rectHSNorm (S n).stableDim
    (matrixFrameLift (S n).stableTargetFrame (Yp.val n) * (S n).stableUnitary.val -
      (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (X.val n))
  have he : Tendsto (fun n => em n + ep n) L (𝓝 0) :=
    matrixThom_anchoredScale_common_unitary_tendsto dims A D F R hDA U hU ε S L hε hε0 hBA
  have hem : Tendsto em L (𝓝 0) := squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => le_add_of_nonneg_right (rectHSNorm_nonneg _ _)) he
  have hep : Tendsto ep L (𝓝 0) := squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => le_add_of_nonneg_left (rectHSNorm_nonneg _ _)) he
  have hXm : Tendsto (fun n => hsNorm (Xm.val n - (1 / 2 : ℂ) • 1)) L (𝓝 0) :=
    hX.congr' (Eventually.of_forall fun n => (hsNorm_unitaryPullback_sub_scalar (U n) (X.val n) (1 / 2)).symm)
  have hm := matrixThom_scalar_transport_tendsto_general dims S L hε Xm Ym (1 / 2) hXm hem
  have hp := matrixThom_scalar_transport_tendsto_general dims S L hε X Yp (1 / 2) hX hep
  change Tendsto (fun n => hsNorm (Ym.val n - (1 / 2 : ℂ) • 1) +
    hsNorm (Yp.val n - (1 / 2 : ℂ) • 1)) L (𝓝 0)
  simpa only [add_zero] using hm.add hp

end ThomGame.Analysis
