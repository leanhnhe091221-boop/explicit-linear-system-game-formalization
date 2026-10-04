module

public import ThomGame.Analysis.MatrixPartitionUnitaryTuple

/-!
# Unitary reduction on every block of a projection partition

Every corner is completed to an actual unitary on its range. No block
is replaced by its identity, so the error is exactly twice the pinching
defect and does not incur a bad-block trace term.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

theorem exists_matrixPartition_reducing_unitary (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Matrix.unitaryGroup ι ℂ) :
    ∃ W : Matrix.unitaryGroup ι ℂ,
      (∀ i, Commute (E i) W.val) ∧
      rectHSNorm r (W.val - U.val) ^ 2 =
        2 * rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 := by
  classical
  have hex (i : μ) : ∃ Y : Matrix ι ι ℂ,
      Yᴴ * Y = E i ∧ Y * Yᴴ = E i ∧
      rectHSNorm r (Y - E i * U.val * E i) ^ 2 =
        matrixTraceReal r (E i - (E i * U.val * E i)ᴴ * (E i * U.val * E i)) := by
    obtain ⟨Y, _, hi, hf, _, _, _, hd, _⟩ := exists_matrixCorner_unitary_pair r (hE i) U
    exact ⟨Y, hi, hf, hd⟩
  choose Y hi hf hd using hex
  let W : Matrix.unitaryGroup ι ℂ :=
    ⟨∑ i, Y i, matrixCorner_sum_mem_unitary E Y hE horth hsum hi hf⟩
  have hl i := (matrixCorner_gram_support (hE i) (hi i) (hf i)).1
  have hr i := (matrixCorner_gram_support (hE i) (hi i) (hf i)).2
  refine ⟨W, ?_, ?_⟩
  · intro i
    show E i * (∑ j, Y j) = (∑ j, Y j) * E i
    rw [matrixCorner_sum_block_left E Y horth hl, matrixCorner_sum_block_right E Y horth hr]
  · change rectHSNorm r ((∑ i, Y i) - U.val) ^ 2 = _
    rw [rectHSNorm_corner_correction_pythagoras r E Y hE horth hl hr]
    simp_rw [hd]
    rw [← rectHSNorm_unitary_pinching_defect_sum r E hE horth hsum U]
    ring

theorem exists_matrixPartition_reducing_tuple {d h : Nat} [NeZero h] (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Fin h → UnitaryMatrix d) :
    ∃ W : Fin h → UnitaryMatrix d,
      (∀ i j, Commute (E i) (W j).val) ∧
      (∑ j, hsNorm ((W j).val - (U j).val) ^ 2) =
        4 * (h : ℝ) * ∑ i, matrixCoordinateEnergy U (E i) := by
  choose W hred hdist using fun j => exists_matrixPartition_reducing_unitary d E hE horth hsum (U j)
  refine ⟨W, (fun i j => hred j i), ?_⟩
  have he := matrixCoordinateEnergy_partition_identity E hE horth hsum U
  have hd : (∑ j, hsNorm ((W j).val - (U j).val) ^ 2) =
      2 * ∑ j, hsNorm ((U j).val - matrixBlockPinch E (U j).val) ^ 2 := by
    simp only [← rectHSNorm_eq_hsNorm, hdist, Finset.mul_sum]
  linarith only [he, hd]

end ThomGame.Analysis
