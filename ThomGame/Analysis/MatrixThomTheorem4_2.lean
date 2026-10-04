module

public import ThomGame.Analysis.MatrixThomAnchorConcentration
public import ThomGame.Analysis.MatrixThomCorrectedConcentration
public import ThomGame.Analysis.MatrixThomReverseConcentration

/-!
# Thom Theorem 4.2 for the actual matrix tracial quotient

Coordinate inclusions, exact commutation with the common coordinate
algebra, and the stated anchor imply equality under every conjugation.
All block data, near-inclusion errors, and relative corrections are
constructed inside the proof. No concentration, reverse inclusion,
spectral-gap assumption, or positivity of corrected dimensions is
supplied as an extra hypothesis. The result holds for any filter.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (hDA : ∀ n, D n ≤ A n) {h : Nat} (U : (n : ι) → Fin h → UnitaryMatrix (dims n))
    (hU : ∀ n j X, X ∈ D n → (U n j).val * X = X * (U n j).val)

include hDA hU in
theorem matrixThom_theorem_4_2_of_internal_inclusions
    (L : Filter ι)
    (hincl : ∀ j, matrixInternalQuotient dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) L ≤
      matrixInternalQuotient dims A L)
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L) :
    ∀ j, matrixInternalQuotient dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) L =
      matrixInternalQuotient dims A L := by
  let F := fun n => Classical.choice (exists_matrixSubalgebraStarBlocks (D n))
  let R := fun n => Classical.choice
    (exists_matrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
  choose ε hε0 hε hBA using fun j => exists_matrixNearInclusion_errors_of_internal_le dims
    (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) A (fun n => NeZero.pos (dims n)) L (hincl j)
  let S := fun j n => Classical.choice (exists_matrixThomSpectralData (A n)
    (matrixUnitaryPullbackAlgebra (A n) (U n j)) (D n) (hDA n)
    (matrixUnitaryPullback_contains_common (A n) (U n j) (D n) (hDA n) (hU n j)) (hε0 j n) (hBA j n))
  have hX := matrixThom_anchoredScale_half_of_corrections dims A D F R hDA U hU ε S L hε hε0 hBA hanchor
  intro j
  apply le_antisymm (hincl j)
  apply (matrixInternal_le_iff_nearInclusionError_tendsto dims A
    (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) (fun n => NeZero.pos (dims n)) L).mpr
  have hc := matrixThom_correctedScale_concentration dims A D F R hDA (fun n => U n j)
    (fun n => hU n j) (ε j) (S j) L (hε j) (hε0 j) (hBA j) hX
  exact matrixThom_reverseInclusion_original_tendsto dims (S j)
    (fun n => matrixUnitaryPullbackBlocks (A n) (U n j) (matrixSubalgebraComplementaryBlocks (A n) (R n)))
    R (fun n => matrixUnitaryPullback_contains_common (A n) (U n j) (D n) (hDA n) (hU n j)) F
    (fun n => matrixAnchoredScaleCoefficients (D n) (A n) (F n) (R n) (hDA n))
    (fun n => matrixAnchoredScaleCoefficients_pos (D n) (A n) (F n) (R n) (hDA n))
    L (hε j) (hε0 j) (hBA j) hc

include hDA hU in
theorem matrixThom_theorem_4_2
    (L : Filter ι)
    (hincl : ∀ j, (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L)
        (unitarySequenceToAlgebra dims L (fun n => U n j))).symm.toStarAlgHom ≤
      matrixInternalQuotient dims A L)
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L) :
    ∀ j, (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L)
        (unitarySequenceToAlgebra dims L (fun n => U n j))).symm.toStarAlgHom =
      matrixInternalQuotient dims A L := by
  have hincl' j : matrixInternalQuotient dims
      (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) L ≤ matrixInternalQuotient dims A L := by
    rw [matrixInternal_unitaryPullback_eq]
    exact hincl j
  intro j
  rw [← matrixInternal_unitaryPullback_eq]
  exact matrixThom_theorem_4_2_of_internal_inclusions dims A D hDA U hU L hincl' hanchor j

end ThomGame.Analysis
