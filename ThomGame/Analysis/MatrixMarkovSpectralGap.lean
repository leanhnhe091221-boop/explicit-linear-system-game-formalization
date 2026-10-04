module

public import ThomGame.Analysis.HilbertSpectralGap
public import ThomGame.Analysis.MatrixNormalRelativeExpectation

/-!
# Spectral gap estimates for the actual matrix Markov maps

The gap is the quadratic-form inequality on the orthogonal complement
of the actual relative-commutant trace space. Under that explicit
condition, the induced powers satisfy ALT (2.4). Constant coordinate
powers induce precisely these Hilbert powers, so mixed-norm transfer
also gives the coordinate ultralimit estimate needed for diagonalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i)

theorem matrixUniformMarkovPower_sequence_succ (k : Nat) (A : BoundedMatrixSequence dims) :
    (matrixUniformMarkovPower dims U hd (fun _ => k + 1)).sequenceMap A =
      (matrixUniformLazyMarkov dims U hd).sequenceMap
        ((matrixUniformMarkovPower dims U hd (fun _ => k)).sequenceMap A) := by
  apply Subtype.ext
  funext i
  change (matrixLazyMarkov (U i) ^ (k + 1)) (A.val i) =
    (matrixUniformLazyMarkov dims U hd).toLinearMap i ((matrixLazyMarkov (U i) ^ k) (A.val i))
  rw [pow_succ', Module.End.mul_apply, matrixUniformLazyMarkov_apply]

theorem matrixUniformMarkovPower_quotient_const (L : Filter ι) (k : Nat)
    (x : MatrixTracialQuotient dims L) :
    (matrixUniformMarkovPower dims U hd (fun _ => k)).quotientMap L x =
      (matrixQuotientLazyMarkov dims U hd L ^ k) x := by
  induction k with
  | zero =>
      obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
      rfl
  | succ k ih =>
      obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
      rw [UniformMatrixMap.quotientMap_mk, matrixUniformMarkovPower_sequence_succ,
        ← UniformMatrixMap.quotientMap_mk, pow_succ', Module.End.mul_apply, ← ih,
        UniformMatrixMap.quotientMap_mk]
      rfl

theorem matrixUniformMarkovPower_hilbert_const (L : Ultrafilter ι) (k : Nat) :
    (matrixUniformMarkovPower dims U hd (fun _ => k)).hilbertMap hd L =
      ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ k := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on (matrixHilbertEmbedding_dense dims hd L) (by fun_prop) (by fun_prop)
  intro ξ hξ
  obtain ⟨x, rfl⟩ := hξ
  rw [UniformMatrixMap.hilbertMap_embedding, matrixUniformMarkovPower_quotient_const]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', mul_apply_eq_comp, ← ih]
      exact (UniformMatrixMap.hilbertMap_embedding _ _ _ _).symm

def MatrixMarkovSpectralGap (L : Ultrafilter ι) (κ : ℝ) : Prop :=
  0 < κ ∧ κ < 1 ∧ ∀ ξ ∈ (matrixRelativeCommutantTraceSubspace dims U hd L)ᗮ,
    κ * ‖ξ‖ ^ 2 ≤ (inner ℂ ξ ((1 - (matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ξ)).re

section NatIndex

variable (dims : Nat → Nat) (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
  (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hgap

include hL in
theorem matrixMarkov_pow_sub_projection_norm_le (j : Nat) :
    ‖((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ j - matrixMarkovProjection dims U hd L‖ ≤
      (1 - κ) ^ j := by
  apply spectralGap_pow_sub_projection_norm_le _ (matrixLazyMarkov_hilbertMap_nonneg dims U hd L) κ hgap.2.1.le
  simpa only [← matrixRelativeCommutantTraceSubspace_eq_fixed dims U hd L hL] using hgap.2.2

include hL in
theorem matrixMarkov_pow_sub_pow_norm_le (j k : Nat) (hj : 0 < j) (hjk : j ≤ k) :
    ‖((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ k -
      ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ j‖ ≤ (1 - κ) ^ j := by
  apply spectralGap_pow_sub_pow_norm_le _ (matrixLazyMarkov_hilbertMap_nonneg dims U hd L) κ hgap.1.le hgap.2.1.le
    ?_ j k hj hjk
  simpa only [← matrixRelativeCommutantTraceSubspace_eq_fixed dims U hd L hL] using hgap.2.2

theorem matrixMarkov_pow_expectation_error (j : Nat) (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L
      ((matrixUniformMarkovPower dims U hd (fun _ => j)).quotientMap (L : Filter Nat) x -
        matrixRelativeExpectation dims U hd L hL x)‖ ≤
      (1 - κ) ^ j * ‖matrixHilbertEmbedding dims hd L x‖ := by
  rw [map_sub, matrixRelativeExpectation_embedding, ← UniformMatrixMap.hilbertMap_embedding,
    matrixUniformMarkovPower_hilbert_const]
  exact (((matrixUniformLazyMarkov dims U hd).hilbertMap hd L ^ j - matrixMarkovProjection dims U hd L).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (matrixMarkov_pow_sub_projection_norm_le dims U hd L hL κ hgap j) (norm_nonneg _))

include hgap in
theorem matrixMarkov_powerDifference_finiteToHilbert_norm_le (j k : Nat) (hj : 0 < j) (hjk : j ≤ k) :
    ‖((matrixUniformMarkovPower dims U hd (fun _ => k)).sub
      (matrixUniformMarkovPower dims U hd (fun _ => j))).finiteToHilbert hd L hL‖ ≤ (1 - κ) ^ j := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (sub_nonneg.mpr hgap.2.1.le) j)
  intro A
  rw [UniformMatrixMap.sub_finiteToHilbert, sub_apply, UniformMatrixMap.finiteToHilbert_vector,
    UniformMatrixMap.finiteToHilbert_vector, matrixUniformMarkovPower_hilbert_const, matrixUniformMarkovPower_hilbert_const]
  have hv : ‖matrixFiniteVector dims hd L A‖ ≤ ‖A‖ := by
    change ‖A.val (matrixHilbertEmbedding dims hd L 1)‖ ≤ ‖A.val‖
    simpa only [matrixUnitVector_norm, mul_one] using A.val.le_opNorm (matrixHilbertEmbedding dims hd L 1)
  exact (((((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ k -
    ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ^ j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (matrixMarkov_pow_sub_pow_norm_le dims U hd L hL κ hgap j k hj hjk)
        (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hv (pow_nonneg (sub_nonneg.mpr hgap.2.1.le) j))

include hL in
theorem matrixMarkov_powerDifference_mixedNormLimit_le (j k : Nat) (hj : 0 < j) (hjk : j ≤ k) :
    ((matrixUniformMarkovPower dims U hd (fun _ => k)).sub
      (matrixUniformMarkovPower dims U hd (fun _ => j))).mixedNormLimit hd L ≤ (1 - κ) ^ j := by
  rw [← UniformMatrixMap.finiteToHilbert_norm_eq_limit _ hd L hL]
  exact matrixMarkov_powerDifference_finiteToHilbert_norm_le dims U hd L hL κ hgap j k hj hjk

end NatIndex
end ThomGame.Analysis
