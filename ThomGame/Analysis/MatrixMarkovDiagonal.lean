module

public import ThomGame.Analysis.PositiveFilterDiagonal
public import ThomGame.Analysis.MatrixMarkovSpectralGap
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual diagonal powers of the matrix Markov maps

At each finite depth, all triangular pairs of powers obey the spectral
gap bound with a positive geometric tolerance. The selected positive
depth tends to infinity and retains its selected-stage certificate.
Every diverging smaller exponent has the same limiting difference
bound against each fixed positive power.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n)

noncomputable def matrixMarkovPowerDistance (j k n : Nat) : ℝ :=
  ((matrixUniformMarkovPower dims U hd (fun _ => k)).sub
    (matrixUniformMarkovPower dims U hd (fun _ => j))).coordinateMixedNorm hd n

def matrixMarkovDiagonalRequirements (κ : ℝ) (m n : Nat) : Prop :=
  ∀ j k : Nat, 0 < j → j ≤ k → k ≤ m →
    matrixMarkovPowerDistance dims U hd j k n ≤ (1 - κ) ^ j + (1 / 2 : ℝ) ^ m

noncomputable def matrixMarkovDiagonalPower (κ : ℝ) : Nat → Nat :=
  positiveDiagonalDepth (matrixMarkovDiagonalRequirements dims U hd κ)

theorem matrixMarkovDiagonalPower_pos (κ : ℝ) (n : Nat) :
    0 < matrixMarkovDiagonalPower dims U hd κ n :=
  positiveDiagonalDepth_pos _ n

variable (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
  (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hL hgap

theorem matrixMarkovPowerDistance_eventually_le (j k : Nat) (hj : 0 < j) (hjk : j ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in (L : Filter Nat), matrixMarkovPowerDistance dims U hd j k n ≤ (1 - κ) ^ j + ε := by
  have hb := matrixMarkov_powerDifference_mixedNormLimit_le dims U hd L hL κ hgap j k hj hjk
  exact (((matrixUniformMarkovPower dims U hd (fun _ => k)).sub
    (matrixUniformMarkovPower dims U hd (fun _ => j))).coordinateMixedNorm_tendsto hd L).eventually_le_const
      (hb.trans_lt (lt_add_of_pos_right _ hε))

theorem matrixMarkovDiagonalRequirements_eventually (m : Nat) :
    ∀ᶠ n in (L : Filter Nat), matrixMarkovDiagonalRequirements dims U hd κ m n := by
  have hp : ∀ᶠ n in (L : Filter Nat), ∀ (j k : Fin (m + 1)), 0 < j.val → j.val ≤ k.val →
      matrixMarkovPowerDistance dims U hd j.val k.val n ≤ (1 - κ) ^ j.val + (1 / 2 : ℝ) ^ m := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    by_cases hj : 0 < j.val
    · by_cases hjk : j.val ≤ k.val
      · exact (matrixMarkovPowerDistance_eventually_le dims U hd L hL κ hgap j.val k.val hj hjk
          _ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m)).mono (fun _ hn _ _ => hn)
      · exact Eventually.of_forall (fun _ _ h => (hjk h).elim)
    · exact Eventually.of_forall (fun _ h => (hj h).elim)
  filter_upwards [hp] with n hn
  intro j k hj hjk hkm
  exact hn ⟨j, by omega⟩ ⟨k, by omega⟩ hj hjk

theorem matrixMarkovDiagonalPower_tendsto :
    Tendsto (matrixMarkovDiagonalPower dims U hd κ) (L : Filter Nat) atTop :=
  positiveDiagonalDepth_tendsto _ (L : Filter Nat) hL
    (matrixMarkovDiagonalRequirements_eventually dims U hd L hL κ hgap)

theorem matrixMarkovDiagonalPower_spec_eventually :
    ∀ᶠ n in (L : Filter Nat), matrixMarkovDiagonalRequirements dims U hd κ
      (matrixMarkovDiagonalPower dims U hd κ n) n :=
  positiveDiagonalDepth_spec_eventually _ (L : Filter Nat) hL
    (matrixMarkovDiagonalRequirements_eventually dims U hd L hL κ hgap)

theorem matrixMarkovDiagonalPower_tolerance_tendsto :
    Tendsto (fun n => (1 / 2 : ℝ) ^ matrixMarkovDiagonalPower dims U hd κ n)
      (L : Filter Nat) (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp
      (matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap)

theorem matrixMarkov_subDiagonal_difference_mixedNormLimit_le (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n)
    (j : Nat) (hj : 0 < j) :
    ((matrixUniformMarkovPower dims U hd k).sub
      (matrixUniformMarkovPower dims U hd (fun _ => j))).mixedNormLimit hd L ≤ (1 - κ) ^ j := by
  have hr := (matrixMarkovDiagonalPower_tolerance_tendsto dims U hd L hL κ hgap).const_add ((1 - κ) ^ j)
  rw [add_zero] at hr
  apply le_of_tendsto_of_tendsto
    (((matrixUniformMarkovPower dims U hd k).sub
      (matrixUniformMarkovPower dims U hd (fun _ => j))).coordinateMixedNorm_tendsto hd L) hr
  filter_upwards [matrixMarkovDiagonalPower_spec_eventually dims U hd L hL κ hgap,
    hk.eventually (eventually_ge_atTop j), hkle] with n hn hjk hkl
  exact hn j (k n) hj hjk hkl

theorem matrixMarkov_subDiagonal_difference_finiteToHilbert_norm_le (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n)
    (j : Nat) (hj : 0 < j) :
    ‖((matrixUniformMarkovPower dims U hd k).sub
      (matrixUniformMarkovPower dims U hd (fun _ => j))).finiteToHilbert hd L hL‖ ≤ (1 - κ) ^ j := by
  rw [UniformMatrixMap.finiteToHilbert_norm_eq_limit]
  exact matrixMarkov_subDiagonal_difference_mixedNormLimit_le dims U hd L hL κ hgap k hk hkle j hj

theorem matrixMarkov_subDiagonal_power_error (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n)
    (j : Nat) (hj : 0 < j) (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L
      ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) x -
        (matrixUniformMarkovPower dims U hd (fun _ => j)).quotientMap (L : Filter Nat) x)‖ ≤
      (1 - κ) ^ j * ‖matrixFiniteEmbedding dims hd L x‖ := by
  have hb := ((matrixUniformMarkovPower dims U hd k).sub
    (matrixUniformMarkovPower dims U hd (fun _ => j))).finiteToHilbert_apply_norm_le_limit hd L hL
      (matrixFiniteEmbedding dims hd L x)
  rw [UniformMatrixMap.finiteToHilbert_embedding, UniformMatrixMap.sub_quotientMap] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (matrixMarkov_subDiagonal_difference_mixedNormLimit_le dims U hd L hL κ hgap k hk hkle j hj)
      (norm_nonneg _))

end ThomGame.Analysis
