module

public import ThomGame.Analysis.MatrixUnitaryPinchingEnergy

/-!
# Actual doubled unitaries reducing a prescribed projection partition

The distinguished bad block is set to its identity. On every other
block the pair averages to the compression of the original unitary.
Each global perturbation costs at most twice the pinching defect plus
four times the bad-block trace, as used in ALT Lemma 4.2.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

theorem rectHSNorm_unitary_partition_correction_le (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Matrix.unitaryGroup ι ℂ) (bad : μ) (Y : μ → Matrix ι ι ℂ)
    (hi : ∀ i, (Y i)ᴴ * Y i = E i) (hf : ∀ i, Y i * (Y i)ᴴ = E i) (hbad : Y bad = E bad)
    (hgood : ∀ i, i ≠ bad → rectHSNorm r (Y i - E i * U.val * E i) ^ 2 =
      matrixTraceReal r (E i - (E i * U.val * E i)ᴴ * (E i * U.val * E i))) :
    rectHSNorm r ((∑ i, Y i) - U.val) ^ 2 ≤
      2 * rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 + 4 * matrixTraceReal r (E bad) := by
  classical
  have hbound : (∑ i, rectHSNorm r (Y i - E i * U.val * E i) ^ 2) ≤
      (∑ i, matrixTraceReal r (E i - (E i * U.val * E i)ᴴ * (E i * U.val * E i))) +
        4 * matrixTraceReal r (E bad) := by
    calc
      _ ≤ ∑ i, (matrixTraceReal r (E i - (E i * U.val * E i)ᴴ * (E i * U.val * E i)) +
          if i = bad then 4 * matrixTraceReal r (E bad) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hib : i = bad
        · subst i
          rw [hbad, ite_eq_left rfl]
          have hd := matrixTraceReal_nonneg r (sub_nonneg.mpr (matrixUnitary_compression_gram_le U (hE bad)))
          have hb := rectHSNorm_unitary_bad_corner_le r U (hE bad)
          linarith only [hd, hb]
        · rw [ite_eq_right hib, add_zero]
          exact (hgood i hib).le
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [← rectHSNorm_unitary_pinching_defect_sum r E hE horth hsum U] at hbound
  rw [rectHSNorm_corner_correction_pythagoras r E Y hE horth
    (fun i => (matrixCorner_gram_support (hE i) (hi i) (hf i)).1)
    (fun i => (matrixCorner_gram_support (hE i) (hi i) (hf i)).2)]
  linarith only [hbound]

theorem exists_matrixPartition_unitary_pair (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Matrix.unitaryGroup ι ℂ) (bad : μ) :
    ∃ V W : Matrix.unitaryGroup ι ℂ,
      (∀ i, Commute (E i) V.val) ∧ (∀ i, Commute (E i) W.val) ∧
      E bad * V.val = E bad ∧ E bad * W.val = E bad ∧
      (∀ i, i ≠ bad → E i * V.val + E i * W.val = (2 : ℂ) • (E i * U.val * E i)) ∧
      rectHSNorm r (V.val - U.val) ^ 2 ≤
        2 * rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 + 4 * matrixTraceReal r (E bad) ∧
      rectHSNorm r (W.val - U.val) ^ 2 ≤
        2 * rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 + 4 * matrixTraceReal r (E bad) := by
  classical
  choose v w hvi hvf hwi hwf hmean hvd hwd using fun i => exists_matrixCorner_unitary_pair r (hE i) U
  let v' : μ → Matrix ι ι ℂ := fun i => if i = bad then E i else v i
  let w' : μ → Matrix ι ι ℂ := fun i => if i = bad then E i else w i
  have hreplace (Z : μ → Matrix ι ι ℂ) (hZi : ∀ i, (Z i)ᴴ * Z i = E i)
      (hZf : ∀ i, Z i * (Z i)ᴴ = E i) (i : μ) :
      (if i = bad then E i else Z i)ᴴ * (if i = bad then E i else Z i) = E i ∧
      (if i = bad then E i else Z i) * (if i = bad then E i else Z i)ᴴ = E i := by
    split_ifs
    · simp only [(hE i).isSelfAdjoint.isHermitian.eq, (hE i).isIdempotentElem.eq, and_self]
    · exact ⟨hZi i, hZf i⟩
  have hvi' i : (v' i)ᴴ * v' i = E i := (hreplace v hvi hvf i).1
  have hvf' i : v' i * (v' i)ᴴ = E i := (hreplace v hvi hvf i).2
  have hwi' i : (w' i)ᴴ * w' i = E i := (hreplace w hwi hwf i).1
  have hwf' i : w' i * (w' i)ᴴ = E i := (hreplace w hwi hwf i).2
  let V : Matrix.unitaryGroup ι ℂ := ⟨∑ i, v' i, matrixCorner_sum_mem_unitary E v' hE horth hsum hvi' hvf'⟩
  let W : Matrix.unitaryGroup ι ℂ := ⟨∑ i, w' i, matrixCorner_sum_mem_unitary E w' hE horth hsum hwi' hwf'⟩
  have hvl i : E i * v' i = v' i := (matrixCorner_gram_support (hE i) (hvi' i) (hvf' i)).1
  have hvr i : v' i * E i = v' i := (matrixCorner_gram_support (hE i) (hvi' i) (hvf' i)).2
  have hwl i : E i * w' i = w' i := (matrixCorner_gram_support (hE i) (hwi' i) (hwf' i)).1
  have hwr i : w' i * E i = w' i := (matrixCorner_gram_support (hE i) (hwi' i) (hwf' i)).2
  refine ⟨V, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show E i * (∑ j, v' j) = (∑ j, v' j) * E i
    rw [matrixCorner_sum_block_left E v' horth hvl, matrixCorner_sum_block_right E v' horth hvr]
  · intro i
    show E i * (∑ j, w' j) = (∑ j, w' j) * E i
    rw [matrixCorner_sum_block_left E w' horth hwl, matrixCorner_sum_block_right E w' horth hwr]
  · change E bad * (∑ i, v' i) = E bad
    rw [matrixCorner_sum_block_left E v' horth hvl]
    simp [v']
  · change E bad * (∑ i, w' i) = E bad
    rw [matrixCorner_sum_block_left E w' horth hwl]
    simp [w']
  · intro i hib
    change E i * (∑ j, v' j) + E i * (∑ j, w' j) = _
    rw [matrixCorner_sum_block_left E v' horth hvl, matrixCorner_sum_block_left E w' horth hwl]
    simpa only [v', w', ite_eq_right hib] using hmean i
  · apply rectHSNorm_unitary_partition_correction_le r E hE horth hsum U bad v' hvi' hvf' (by simp [v'])
    intro i hib
    simpa only [v', ite_eq_right hib] using hvd i
  · apply rectHSNorm_unitary_partition_correction_le r E hE horth hsum U bad w' hwi' hwf' (by simp [w'])
    intro i hib
    simpa only [w', ite_eq_right hib] using hwd i

end ThomGame.Analysis
