module

public import ThomGame.Analysis.SlowPowerDiagonal
public import ThomGame.Analysis.MatrixMarkovDuplication
public import ThomGame.Analysis.MatrixMarkovPerturbation
public import ThomGame.Analysis.MatrixMarkovDiagonalExpectation
public import ThomGame.Analysis.MatrixALTQuotientRepresentatives

/-!
# Corrected diagonal powers induce the original expectation

The actual tuple edits control the one-step mixed norm. A selected
positive slow exponent makes the accumulated edit tend to zero while
remaining below the original Markov diagonal. Thus the corrected powers
induce the original relative-commutant expectation.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators

section Perturbation

variable {ι : Type*} (dims : ι → Nat) {h : Nat}
  (U V : (k : ι) → Fin h → UnitaryMatrix (dims k))

noncomputable def matrixMarkovTupleEditBound (k : ι) : ℝ :=
  4 * lazyMarkovWeight h * ∑ j, hsNorm ((U k j).val - (V k j).val)

theorem matrixMarkovTupleEditBound_nonneg (k : ι) :
    0 ≤ matrixMarkovTupleEditBound dims U V k :=
  mul_nonneg (mul_nonneg (by norm_num) (lazyMarkovWeight_nonneg h))
    (Finset.sum_nonneg (fun j _ => hsNorm_nonneg _))

theorem matrixMarkovTupleEditBound_tendsto_zero (L : Filter ι)
    (hUV : ∀ j, Tendsto (fun k => hsNorm ((U k j).val - (V k j).val)) L (𝓝 0)) :
    Tendsto (matrixMarkovTupleEditBound dims U V) L (𝓝 0) := by
  change Tendsto (fun k => 4 * lazyMarkovWeight h * ∑ j, hsNorm ((U k j).val - (V k j).val)) L (𝓝 0)
  have ht := (tendsto_finsetSum Finset.univ (fun j _ => hUV j)).const_mul (4 * lazyMarkovWeight h)
  simpa only [Finset.sum_const_zero, mul_zero] using ht

theorem matrixMarkovTupleEditBound_tendsto_zero_of_sum_sq (L : Filter ι)
    (hUV : Tendsto (fun k => ∑ j, hsNorm ((U k j).val - (V k j).val) ^ 2) L (𝓝 0)) :
    Tendsto (matrixMarkovTupleEditBound dims U V) L (𝓝 0) :=
  matrixMarkovTupleEditBound_tendsto_zero dims U V L
    (hsNorm_tendsto_zero_of_sum_sq dims L (fun k j => (U k j).val - (V k j).val) hUV)

variable [NeZero h] (hd : ∀ k, 0 < dims k)

theorem matrixUniformMarkovPower_sub_mixedNorm_le (N : ι → Nat) (k : ι) :
    ((matrixUniformMarkovPower dims U hd N).sub
      (matrixUniformMarkovPower dims V hd N)).coordinateMixedNorm hd k ≤
        (N k : ℝ) * matrixMarkovTupleEditBound dims U V k := by
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  apply matrixMixedNorm_le _ _
    (mul_nonneg (Nat.cast_nonneg _) (matrixMarkovTupleEditBound_nonneg dims U V k))
  intro X
  exact matrixLazyMarkov_pow_sub_hsNorm_le (U k) (V k) _
    (matrixMarkovTupleEditBound_nonneg dims U V k)
    (matrixLazyMarkov_sub_hsNorm_le (U k) (V k)) (N k) X

theorem matrixUniformMarkovPower_sub_mixedNorm_tendsto_zero (N : ι → Nat) (L : Filter ι)
    (hN : Tendsto (fun k => (N k : ℝ) * matrixMarkovTupleEditBound dims U V k) L (𝓝 0)) :
    Tendsto (((matrixUniformMarkovPower dims U hd N).sub
      (matrixUniformMarkovPower dims V hd N)).coordinateMixedNorm hd) L (𝓝 0) :=
  squeeze_zero
    (((matrixUniformMarkovPower dims U hd N).sub
      (matrixUniformMarkovPower dims V hd N)).coordinateMixedNorm_nonneg hd)
    (matrixUniformMarkovPower_sub_mixedNorm_le dims U V hd N) hN

end Perturbation

theorem exists_matrixALT_corrected_power_expectation (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ)
    (T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k))
    (hTU : Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
      (L : Filter Nat) (𝓝 0)) :
    ∃ N : Nat → Nat, (∀ k, 0 < N k) ∧ Tendsto N (L : Filter Nat) atTop ∧
      (∀ᶠ k in (L : Filter Nat), N k ≤ matrixMarkovDiagonalPower dims U hd κ k) ∧
      Tendsto (((matrixUniformMarkovPower dims T hd N).sub
        (matrixUniformMarkovPower dims U hd N)).coordinateMixedNorm hd) (L : Filter Nat) (𝓝 0) ∧
      (matrixUniformMarkovPower dims T hd N).quotientMap (L : Filter Nat) =
        matrixRelativeExpectation dims U hd L hL := by
  let V := fun k => Fin.append (U k) (U k)
  let ε := matrixMarkovTupleEditBound dims T V
  let ell := matrixMarkovDiagonalPower dims U hd κ
  let N := slowDivergingPower ell ε
  have hε : Tendsto ε (L : Filter Nat) (𝓝 0) :=
    matrixMarkovTupleEditBound_tendsto_zero_of_sum_sq dims T V (L : Filter Nat) hTU
  have hell : Tendsto ell (L : Filter Nat) atTop :=
    matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap
  have hN : Tendsto N (L : Filter Nat) atTop :=
    slowDivergingPower_tendsto ell ε (L : Filter Nat) hL hell hε
  have hle : ∀ᶠ k in (L : Filter Nat), N k ≤ ell k :=
    slowDivergingPower_le_eventually ell ε (L : Filter Nat) hL hell hε
  have hprod : Tendsto (fun k => (N k : ℝ) * ε k) (L : Filter Nat) (𝓝 0) :=
    slowDivergingPower_mul_tendsto_zero ell ε (L : Filter Nat) hL hell hε
      (matrixMarkovTupleEditBound_nonneg dims T V)
  have hnorm := matrixUniformMarkovPower_sub_mixedNorm_tendsto_zero dims T V hd N (L : Filter Nat) hprod
  have hV : matrixUniformMarkovPower dims V hd N = matrixUniformMarkovPower dims U hd N :=
    matrixUniformMarkovPower_append_self dims U hd N
  rw [hV] at hnorm
  refine ⟨N, slowDivergingPower_pos ell ε, hN, hle, hnorm, ?_⟩
  have hsame := ((matrixUniformMarkovPower dims T hd N).quotientMap_eq_iff_mixedNorm_sub_tendsto_zero
    hd L hL (matrixUniformMarkovPower dims U hd N)).mpr hnorm
  exact hsame.trans (matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap N hN hle)

end ThomGame.Analysis
