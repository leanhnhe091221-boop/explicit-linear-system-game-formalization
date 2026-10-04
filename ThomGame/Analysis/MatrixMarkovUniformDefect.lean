module

public import ThomGame.Analysis.MatrixMarkovDefectBound

/-!
# The uniform coordinate defect tends to zero

A maximizing contraction in every coordinate forms an actual bounded
matrix sequence. Its quotient witnesses the Poincare inequality and
the zero energy of the expected output. Thus the attained supremum
defect, not merely each fixed matrix's defect, tends to zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n)

noncomputable def matrixMarkovDefectSequence (κ : ℝ) (k : Nat → Nat) : BoundedMatrixSequence dims := by
  letI : ∀ n, NeZero (dims n) := fun n => ⟨Nat.ne_of_gt (hd n)⟩
  exact ⟨fun n => matrixMarkovDefectMaximizer (U n) κ (k n),
    1, zero_le_one, fun n => matrixMarkovDefectMaximizer_norm_le (U n) κ (k n)⟩

noncomputable def matrixUniformMarkovDefect (κ : ℝ) (k : Nat → Nat) (n : Nat) : ℝ := by
  letI : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
  exact matrixMarkovDefectBound (U n) κ (k n)

omit [NeZero h] in
theorem matrixUniformMarkovDefect_eq_witness (κ : ℝ) (k : Nat → Nat) (n : Nat) :
    matrixUniformMarkovDefect dims U hd κ k n =
      matrixMarkovDefect (U n) κ (k n) ((matrixMarkovDefectSequence dims U hd κ k).val n) := rfl

omit [NeZero h] in
theorem matrixUniformMarkovDefect_nonneg (κ : ℝ) (k : Nat → Nat) (n : Nat) :
    0 ≤ matrixUniformMarkovDefect dims U hd κ k n := by
  let : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
  exact matrixMarkovDefectBound_nonneg (U n) κ (k n)

theorem matrixUniformMarkovDefect_le_two (κ : ℝ) (k : Nat → Nat) (n : Nat) :
    matrixUniformMarkovDefect dims U hd κ k n ≤ 2 := by
  let : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
  exact matrixMarkovDefectBound_le_two (U n) κ (k n)

omit [NeZero h] in
theorem matrixUniformMarkovDefect_distance (κ : ℝ) (k : Nat → Nat) (n : Nat)
    (X : CMatrix (dims n)) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - (matrixLazyMarkov (U n) ^ k n) X) ≤
      (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy (U n) X) + matrixUniformMarkovDefect dims U hd κ k n := by
  let : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
  exact matrixMarkovDefectBound_distance (U n) κ (k n) X hX

omit [NeZero h] in
theorem matrixUniformMarkovDefect_energy (κ : ℝ) (k : Nat → Nat) (n : Nat)
    (X : CMatrix (dims n)) (hX : matrixOpNorm X ≤ 1) :
    Real.sqrt (matrixCoordinateEnergy (U n) ((matrixLazyMarkov (U n) ^ k n) X)) ≤
      matrixUniformMarkovDefect dims U hd κ k n := by
  let : NeZero (dims n) := ⟨Nat.ne_of_gt (hd n)⟩
  exact matrixMarkovDefectBound_energy (U n) κ (k n) X hX

variable (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
  (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hgap in
theorem matrixUniformMarkovDefect_tendsto_zero_of_quotientMap_eq (k : Nat → Nat)
    (hmap : (matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter Nat) =
      matrixRelativeExpectation dims U hd L hL) :
    Tendsto (matrixUniformMarkovDefect dims U hd κ k) (L : Filter Nat) (𝓝 0) := by
  let A := matrixMarkovDefectSequence dims U hd κ k
  let F := matrixUniformMarkovPower dims U hd k
  let x := matrixQuotientMk dims (L : Filter Nat) A
  have hm : F.quotientMap (L : Filter Nat) = matrixRelativeExpectation dims U hd L hL := hmap
  have hdistance := matrixHilbertEmbedding_norm_tendsto dims hd L (A - F.sequenceMap A)
  rw [map_sub, ← UniformMatrixMap.quotientMap_mk, hm] at hdistance
  have hinput := Real.continuous_sqrt.continuousAt.tendsto.comp (matrixCoordinateEnergy_tendsto dims U hd L A)
  have houtput := Real.continuous_sqrt.continuousAt.tendsto.comp
    (matrixCoordinateEnergy_tendsto dims U hd L (F.sequenceMap A))
  rw [← UniformMatrixMap.quotientMap_mk, hm, matrixRelativeExpectation_energy_zero, Real.sqrt_zero] at houtput
  have hpos := (hdistance.sub (hinput.const_mul (Real.sqrt κ)⁻¹)).max
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) (L : Filter Nat) (𝓝 0))
  have hp := matrixRelativeExpectation_poincare dims U hd L hL κ hgap x
  have hz : max (‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ -
      (Real.sqrt κ)⁻¹ * Real.sqrt (matrixMarkovEnergy dims U hd L x)) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr hp)
  change Tendsto _ (L : Filter Nat) (𝓝 (max
    (‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ -
      (Real.sqrt κ)⁻¹ * Real.sqrt (matrixMarkovEnergy dims U hd L x)) 0)) at hpos
  rw [hz] at hpos
  have ht := hpos.max houtput
  rw [max_self] at ht
  exact ht

include hL hgap in
theorem matrixUniformMarkovDefect_subDiagonal_tendsto_zero (k : Nat → Nat)
    (hk : Tendsto k (L : Filter Nat) atTop)
    (hkle : ∀ᶠ n in (L : Filter Nat), k n ≤ matrixMarkovDiagonalPower dims U hd κ n) :
    Tendsto (matrixUniformMarkovDefect dims U hd κ k) (L : Filter Nat) (𝓝 0) :=
  matrixUniformMarkovDefect_tendsto_zero_of_quotientMap_eq dims U hd L hL κ hgap k
    (matrixMarkov_subDiagonal_quotientMap_eq_expectation dims U hd L hL κ hgap k hk hkle)

include hL hgap in
theorem matrixUniformMarkovDefect_diagonal_tendsto_zero :
    Tendsto (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ))
      (L : Filter Nat) (𝓝 0) :=
  matrixUniformMarkovDefect_tendsto_zero_of_quotientMap_eq dims U hd L hL κ hgap _
    (matrixMarkovDiagonalPower_quotientMap_eq_expectation dims U hd L hL κ hgap)

end ThomGame.Analysis
