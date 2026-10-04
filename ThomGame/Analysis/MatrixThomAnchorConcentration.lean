module

public import ThomGame.Analysis.MatrixAnchoredScaleSequence
public import ThomGame.Analysis.MatrixThomAnchoredCommutation
public import ThomGame.Analysis.MatrixInternalNearInclusion
public import ThomGame.Analysis.MatrixInternalUnitaryPullback

/-!
# The actual anchor forces the original median to concentrate at one half

The second theorem constructs all near-inclusion errors and spectral
corrections from genuine internal inclusions. The only anchor assumption
is the stated intersection of the actual internal algebra and tuple
commutant; concentration is a conclusion.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDA : ∀ n, D n ≤ A n) {h : Nat} (U : (n : ι) → Fin h → UnitaryMatrix (dims n))
    (hU : ∀ n j X, X ∈ D n → (U n j).val * X = X * (U n j).val)

include hU in
theorem matrixThom_anchoredScale_half_of_corrections
    (ε : Fin h → ι → ℝ)
    (S : (j : Fin h) → (n : ι) → MatrixThomSpectralData (A n)
      (matrixUnitaryPullbackAlgebra (A n) (U n j)) (D n) (ε j n))
    (L : Filter ι) (hε : ∀ j, Tendsto (ε j) L (𝓝 0)) (hε0 : ∀ j n, 0 ≤ ε j n)
    (hBA : ∀ j n, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (A n) (U n j)) (A n) (ε j n))
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L) :
    Tendsto (fun n => hsNorm (matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) -
      (1 / 2 : ℂ) • 1)) L (𝓝 0) := by
  exact matrixQuotientAnchor_scalar_tendsto dims U L A D
    (matrixAnchoredScaleSequence dims A D F R hDA) (1 / 2) hanchor
    (matrixAnchoredScaleSequence_mem dims A D F R hDA)
    (fun j => matrixThom_anchoredScale_commutator_tendsto dims A D F R hDA (fun n => U n j)
      (fun n => hU n j) (ε j) (S j) L (hε j) (hε0 j) (hBA j))
    (matrixAnchoredScaleSequence_expectation dims A D F R hDA)

include hU in
theorem matrixThom_anchoredScale_half_of_internal_inclusions
    (L : Filter ι)
    (hincl : ∀ j, matrixInternalQuotient dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) L ≤
      matrixInternalQuotient dims A L)
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L) :
    Tendsto (fun n => hsNorm (matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) -
      (1 / 2 : ℂ) • 1)) L (𝓝 0) := by
  choose ε hε0 hε hBA using fun j => exists_matrixNearInclusion_errors_of_internal_le dims
    (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) A (fun n => NeZero.pos (dims n)) L (hincl j)
  let S := fun j n => Classical.choice (exists_matrixThomSpectralData (A n)
    (matrixUnitaryPullbackAlgebra (A n) (U n j)) (D n) (hDA n)
    (matrixUnitaryPullback_contains_common (A n) (U n j) (D n) (hDA n) (hU n j)) (hε0 j n) (hBA j n))
  exact matrixThom_anchoredScale_half_of_corrections dims A D F R hDA U hU ε S L hε hε0 hBA hanchor

include hU in
theorem matrixThom_anchoredScale_half
    (L : Filter ι)
    (hincl : ∀ j, (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L)
        (unitarySequenceToAlgebra dims L (fun n => U n j))).symm.toStarAlgHom ≤
      matrixInternalQuotient dims A L)
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L) :
    Tendsto (fun n => hsNorm (matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n) -
      (1 / 2 : ℂ) • 1)) L (𝓝 0) := by
  apply matrixThom_anchoredScale_half_of_internal_inclusions dims A D F R hDA U hU L _ hanchor
  intro j
  rw [matrixInternal_unitaryPullback_eq]
  exact hincl j

end ThomGame.Analysis
