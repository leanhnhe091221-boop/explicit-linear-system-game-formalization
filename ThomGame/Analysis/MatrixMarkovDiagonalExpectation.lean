module

public import ThomGame.Analysis.MatrixMarkovDiagonal
public import ThomGame.Analysis.UniformMatrixExpectations

/-!
# Diagonal Markov powers induce the relative-commutant expectation

Under the genuine spectral-gap condition, the selected diagonal and
every diverging smaller sequence induce the actual expectation on all
bounded matrix classes. Its range is internal exactly when the
coordinate difference from the prescribed expectations tends to zero
in the operator-to-trace norm. This proves ALT Proposition 2.2.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n)
  (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
  (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hL hgap

theorem matrixMarkov_subDiagonal_expectation_error (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n)
    (j : Nat) (hj : 0 < j) (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L
      ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) x -
        matrixRelativeExpectation dims U hd L hL x)‖ ≤
      (1 - κ) ^ j * (‖matrixFiniteEmbedding dims hd L x‖ + ‖matrixHilbertEmbedding dims hd L x‖) := by
  rw [map_sub, mul_add]
  have hb := matrixMarkov_subDiagonal_power_error dims U hd L hL κ hgap k hk hkle j hj x
  have he := matrixMarkov_pow_expectation_error dims U hd L hL κ hgap j x
  rw [map_sub] at hb he
  exact (norm_sub_le_norm_sub_add_norm_sub _ (matrixHilbertEmbedding dims hd L
    ((matrixUniformMarkovPower dims U hd (fun _ => j)).quotientMap (L : Filter Nat) x)) _).trans
      (add_le_add hb he)

theorem matrixMarkov_subDiagonal_quotientMap_eq_expectation (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n) :
    (matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) =
      matrixRelativeExpectation dims U hd L hL := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply matrixHilbertEmbedding_injective dims hd L
  rw [map_zero]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hgap.2.1.le)
    (by linarith [hgap.1] : 1 - κ < 1)).mul_const
      (‖matrixFiniteEmbedding dims hd L x‖ + ‖matrixHilbertEmbedding dims hd L x‖)
  rw [zero_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (0 : Nat)] with j hj
  exact matrixMarkov_subDiagonal_expectation_error dims U hd L hL κ hgap k hk hkle j hj x

theorem matrixMarkovDiagonalPower_quotientMap_eq_expectation :
    (matrixUniformMarkovPower dims U hd (matrixMarkovDiagonalPower dims U hd κ)).quotientMap (L : Filter Nat) =
      matrixRelativeExpectation dims U hd L hL :=
  matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap _
    (matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap) (Eventually.of_forall (fun _ => le_rfl))

theorem matrixMarkov_subDiagonal_finiteMap_eq_expectation (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n) :
    (matrixUniformMarkovPower dims U hd k).finiteMap hd L hL = matrixFiniteRelativeExpectation dims U hd L hL := by
  apply LinearMap.ext
  intro A
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL A
  rw [UniformMatrixMap.finiteMap_embedding, matrixFiniteRelativeExpectation_embedding,
    matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap k hk hkle]

theorem matrixMarkov_subDiagonal_hilbertMap_eq_projection (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n) :
    (matrixUniformMarkovPower dims U hd k).hilbertMap hd L = matrixMarkovProjection dims U hd L := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (matrixHilbertEmbedding_dense dims hd L).induction_on ξ ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    rw [UniformMatrixMap.hilbertMap_embedding,
      matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap k hk hkle,
      matrixRelativeExpectation_embedding]

theorem matrixMarkov_subDiagonal_range (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n) :
    LinearMap.range ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat)) =
      (matrixRelativeCommutant dims U (L : Filter Nat)).toSubalgebra.toSubmodule := by
  rw [matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap k hk hkle,
    matrixRelativeExpectation_range]

theorem matrixMarkov_subDiagonal_internal_iff (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n)
    (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))) :
    matrixInternalQuotient dims S (L : Filter Nat) = matrixRelativeCommutant dims U (L : Filter Nat) ↔
      Tendsto (((matrixUniformMarkovPower dims U hd k).sub (matrixUniformExpectation dims S hd)).coordinateMixedNorm hd)
        (L : Filter Nat) (𝓝 0) := by
  have hp (x y : MatrixTracialQuotient dims (L : Filter Nat)) :
      matrixUltratrace dims hd L
        (star ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) y) *
          (matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) x) =
      matrixUltratrace dims hd L (star ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) y) * x) := by
    rw [matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap k hk hkle]
    exact matrixRelativeExpectation_pairing dims U hd L hL x _ (matrixRelativeExpectation_mem dims U hd L hL y)
  have he := quotientRange_eq_internal_iff_mixedNorm_tendsto_zero dims S hd L hL
    (matrixUniformMarkovPower dims U hd k) hp
  rw [matrixMarkov_subDiagonal_range dims U hd L hL κ hgap k hk hkle] at he
  constructor
  · intro hS
    exact he.mp (by rw [hS])
  · intro hz
    have hS := he.mpr hz
    apply SetLike.ext
    intro x
    exact (SetLike.ext_iff.mp hS x).symm

theorem matrixMarkovDiagonalPower_internal_iff
    (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))) :
    matrixInternalQuotient dims S (L : Filter Nat) = matrixRelativeCommutant dims U (L : Filter Nat) ↔
      Tendsto (((matrixUniformMarkovPower dims U hd (matrixMarkovDiagonalPower dims U hd κ)).sub
        (matrixUniformExpectation dims S hd)).coordinateMixedNorm hd) (L : Filter Nat) (𝓝 0) :=
  matrixMarkov_subDiagonal_internal_iff dims U hd L hL κ hgap _
    (matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap) (Eventually.of_forall (fun _ => le_rfl)) S

theorem exists_matrixMarkovDiagonal_inducing_expectation :
    ∃ ell : Nat → Nat, (∀ n, 0 < ell n) ∧ Tendsto ell (L : Filter Nat) atTop ∧
      (matrixUniformMarkovPower dims U hd ell).quotientMap (L : Filter Nat) =
        matrixRelativeExpectation dims U hd L hL ∧
      ∀ k : Nat → Nat, Tendsto k (L : Filter Nat) atTop → (∀ᶠ n in (L : Filter Nat), k n ≤ ell n) →
        (matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) =
          matrixRelativeExpectation dims U hd L hL :=
  ⟨matrixMarkovDiagonalPower dims U hd κ, matrixMarkovDiagonalPower_pos dims U hd κ,
    matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap,
    matrixMarkovDiagonalPower_quotientMap_eq_expectation dims U hd L hL κ hgap,
    matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap⟩

end ThomGame.Analysis
