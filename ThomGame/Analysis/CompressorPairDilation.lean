module

public import ThomGame.Analysis.CompressorPairCollection
public import ThomGame.Analysis.FiniteIsometryAverage
public import ThomGame.Analysis.FinitePrimeFivePairPolynomial
public import ThomGame.Analysis.MatrixMarkovPerturbation
public import ThomGame.Analysis.FiniteNoDriftRootWords

/-! Regular dilations for the actual approximate compressor root matrices. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor FinitePrimeFivePair
open scoped BigOperators
variable {d r : ℕ} [NeZero d]

theorem matrixUnitaryConjugation_mul_apply (U V : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryConjugation (U*V) X = matrixUnitaryConjugation U (matrixUnitaryConjugation V X) := by
  simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.mul_val, star_mul, mul_assoc]

theorem matrixConjugation_comp_sub_le (U V W : UnitaryMatrix d) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) {ε : ℝ} (he : unitaryDist (U*V) W ≤ ε) :
    ‖matrixConjugationHilbertEquiv U (matrixConjugationHilbertEquiv V (finiteMatrixHilbertEquiv d X)) -
      matrixConjugationHilbertEquiv W (finiteMatrixHilbertEquiv d X)‖ ≤ 2*ε := by
  simp only [matrixConjugationHilbertEquiv_apply, matrixConjugationHilbert_embedding,
    ← map_sub, finiteMatrixHilbert_norm, ← matrixUnitaryConjugation_mul_apply]
  have ht := matrixUnitaryConjugation_sub_le (U*V) W X
  have hε : 0 ≤ ε := (unitaryDist_nonneg _ _).trans he
  exact ht.trans (by
    change 2 * unitaryDist (U*V) W * matrixOpNorm X ≤ 2*ε
    nlinarith [unitaryDist_nonneg (U*V) W, matrixOpNorm_nonneg X])

def compressorPairMatrices (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (g : FinitePrimeFivePair r) : UnitaryMatrix d :=
  f (compressorPairCanonical root σ g)

def compressorPairAction (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (g : FinitePrimeFivePair r) :=
  matrixConjugationHilbertEquiv (compressorPairMatrices f root σ g)

theorem compressorPairMatrices_mul_defect (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (g k : FinitePrimeFivePair r) :
    unitaryDist (compressorPairMatrices f root σ g * compressorPairMatrices f root σ k)
      (compressorPairMatrices f root σ (g*k)) ≤ 1000000000*δ := by
  simpa only [compressorPairMatrices, map_mul, Nat.cast_ofNat] using
    (compressorPairCanonical_mul_area root σ hr g k).unitaryDist_le f hδ hf

theorem compressorPairMatrices_mul_inv_defect (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (g k : FinitePrimeFivePair r) :
    unitaryDist (compressorPairMatrices f root σ g * (compressorPairMatrices f root σ k)⁻¹)
      (compressorPairMatrices f root σ (g*k⁻¹)) ≤ 2000000000*δ := by
  have hc := ((compressorPairCanonical_inv_area root σ hr k).symm.mul_left
    (compressorPairCanonical root σ g)).trans (compressorPairCanonical_mul_area root σ hr g k⁻¹)
  simpa only [compressorPairMatrices, map_mul, map_inv, Nat.reduceAdd, Nat.cast_ofNat] using hc.unitaryDist_le f hδ hf

theorem compressorPairAction_mul_error (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) (g k : FinitePrimeFivePair r) :
    ‖compressorPairAction f root σ g (compressorPairAction f root σ k (finiteMatrixHilbertEquiv d X)) -
      compressorPairAction f root σ (g*k) (finiteMatrixHilbertEquiv d X)‖ ≤ 2000000000*δ := by
  simpa only [compressorPairAction, ← mul_assoc, show (2:ℝ)*1000000000=2000000000 by norm_num] using
    matrixConjugation_comp_sub_le _ _ _ X hX (compressorPairMatrices_mul_defect f root σ hr hδ hf g k)

theorem compressorPairAction_mul_inv_error (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) (g k : FinitePrimeFivePair r) :
    ‖compressorPairAction f root σ g ((compressorPairAction f root σ k).symm (finiteMatrixHilbertEquiv d X)) -
      compressorPairAction f root σ (g*k⁻¹) (finiteMatrixHilbertEquiv d X)‖ ≤ 4000000000*δ := by
  simpa only [compressorPairAction, matrixConjugationHilbertEquiv_apply,
    matrixConjugationHilbertEquiv_symm_apply, ← mul_assoc,
    show (2:ℝ)*2000000000=4000000000 by norm_num] using
    matrixConjugation_comp_sub_le _ _ _ X hX (compressorPairMatrices_mul_inv_defect f root σ hr hδ hf g k)

theorem compressorPairCanonical_left (root : Root) (σ : Fin r → Coeff) (α : Fin r → ZMod 5) :
    compressorPairCanonical root σ (leftVector α) =
      Word.eval FreeGroup.of (vectorWord (List.finRange r) (fun i => X root (σ i)) α) := by
  simp [compressorPairCanonical, PairCollectionRelations.normal, PairCollectionRelations.A,
    PairCollectionRelations.C, PairCollectionRelations.indices, RelatorEquality.blockProduct,
    leftVector, eval_vectorWord, X]

theorem compressorPairCanonical_right (root : Root) (σ : Fin r → Coeff) (α : Fin r → ZMod 5) :
    compressorPairCanonical root σ (rightVector α) =
      Word.eval FreeGroup.of (vectorWord (List.finRange r) (fun i => X (right root) (σ i)) α) := by
  simp [compressorPairCanonical, PairCollectionRelations.normal, PairCollectionRelations.A,
    PairCollectionRelations.C, PairCollectionRelations.indices, RelatorEquality.blockProduct,
    rightVector, eval_vectorWord, X]

end ThomGame.Analysis
