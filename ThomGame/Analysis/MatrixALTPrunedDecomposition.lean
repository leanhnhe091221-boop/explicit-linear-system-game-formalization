module

public import ThomGame.Analysis.MatrixALTDefectSum
public import ThomGame.Analysis.MatrixALTLemma4_2

/-!
# Actual ALT decomposition with a small bad block

The corrected minimum-rank family supplies all inputs of Lemma 4.2.
Every retained nonzero block has scalar gap kappa squared over 2^28.
The bad trace and the edit of the original doubled tuple have explicit
bounds tending to zero with eta.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

noncomputable def altBlockErrorBound (κ η : ℝ) : ℝ :=
  85248 * η ^ 2 + 6 * (512 / κ) ^ 2 * η

noncomputable def altPrunedTraceBound (κ η : ℝ) : ℝ :=
  16 * η + 16384 * altBlockErrorBound κ η / κ

noncomputable def altPrunedEditBound (κ η : ℝ) : ℝ :=
  4 * altBlockErrorBound κ η + 16 * altPrunedTraceBound κ η + 151552 * η ^ 2

theorem matrixDoubledTuple_perturb_sq_le (U W : Fin h → UnitaryMatrix d)
    (T : Fin (h + h) → UnitaryMatrix d) :
    (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
      2 * (∑ j, hsNorm ((T j).val - (Fin.append W W j).val) ^ 2) +
        4 * ∑ j, hsNorm ((W j).val - (U j).val) ^ 2 := by
  have hj (j : Fin (h + h)) : hsNorm ((T j).val - (Fin.append U U j).val) ^ 2 ≤
      2 * hsNorm ((T j).val - (Fin.append W W j).val) ^ 2 +
        2 * hsNorm ((Fin.append W W j).val - (Fin.append U U j).val) ^ 2 := by
    have he : (T j).val - (Fin.append U U j).val =
        ((T j).val - (Fin.append W W j).val) +
          ((Fin.append W W j).val - (Fin.append U U j).val) := by abel
    rw [he]
    exact rectHSNorm_add_sq_le d _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j
  have hd : (∑ j, hsNorm ((Fin.append W W j).val - (Fin.append U U j).val) ^ 2) =
      2 * ∑ j, hsNorm ((W j).val - (U j).val) ^ 2 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hd] at hs
  linarith only [hs]

structure MatrixALTPrunedDecomposition (U : Fin h → UnitaryMatrix d) (κ η : ℝ) where
  n : Nat
  length_le : n ≤ 8 * d
  E : Option (Fin n) → CMatrix d
  T : Fin (h + h) → UnitaryMatrix d
  projection : ∀ i, IsStarProjection (E i)
  orthogonal : Pairwise (fun i j => E i * E j = 0)
  sum_one : ∑ i, E i = 1
  reducing : ∀ i j, Commute (E i) (T j).val
  bad_identity : ∀ j, E none * (T j).val = E none
  bad_trace : matrixTraceReal d (E none) ≤ altPrunedTraceBound κ η
  perturbation : (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
    (h : ℝ) * altPrunedEditBound κ η
  scalar_gap : ∀ i, E (some i) ≠ 0 → ∀ X : CMatrix d,
    E (some i) * X = X → X * E (some i) = X →
      κ ^ 2 / 2 ^ 28 * hsNorm
        (X - (normalizedTrace X / normalizedTrace (E (some i))) • E (some i)) ^ 2 ≤
        matrixCoordinateEnergy T X

theorem exists_matrixALT_prunedDecomposition [NeZero d] [NeZero h]
    (U : Fin h → UnitaryMatrix d) {κ α η : ℝ} {R : CMatrix d}
    (sel : MatrixALTOrthogonalSelection U κ α η R) (hR : IsStarProjection R)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) : Nonempty (MatrixALTPrunedDecomposition U κ η) := by
  obtain ⟨W, hWred, hWdist⟩ := sel.exists_reducing_tuple U
  let P := matrixProjectionCompletion (fun i => (sel.V i)ᴴ * sel.V i)
  let ξ : Fin sel.n → ℝ := fun i =>
    matrixALTBlockError U W (matrixClosedLowSpectralCut (sel.S i) (κ / 512)) (sel.V i)
  have hP : ∀ i, IsStarProjection (P i) := matrixProjectionCompletion_isStarProjection _
    sel.initial_projection sel.initial_orthogonal
  have horth : Pairwise (fun i j => P i * P j = 0) := matrixProjectionCompletion_orthogonal _
    sel.initial_projection sel.initial_orthogonal
  have hξ (i : Fin sel.n) : 0 ≤ ξ i := matrixALTBlockError_nonneg U W
    (matrixClosedLowSpectralCut_isStarProjection (sel.S i) (κ / 512)) (sel.initial_projection i)
  have hsumξ : (∑ i, ξ i) ≤ altBlockErrorBound κ η := sel.block_error_sum_le U W hWdist
  obtain ⟨E, T, hE, hEorth, hEsum, _, hred, hbad, _, htrace, hdist, _, hgap⟩ :=
    exists_matrixPartition_ALT_lemma4_2 W P hP horth (matrixProjectionCompletion_sum _) hWred
      (show 0 < κ / 1024 by positivity) ξ hξ (fun i q hq hqP hqr =>
        sel.reducing_half_expansion U W hR hκ.le hκ1 i hq hqP hqr)
  have htracebound : matrixTraceReal d (E none) ≤ altPrunedTraceBound κ η := by
    have hb : matrixTraceReal d (P none) ≤ 16 * η := sel.bad_trace
    have hs := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsumξ
      (by norm_num : (0 : ℝ) ≤ 16)) (show 0 ≤ κ / 1024 by positivity)
    have he := htrace.trans (add_le_add hb hs)
    convert he using 1
    unfold altPrunedTraceBound
    field_simp
    ring
  have hdistbound : (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
      (h : ℝ) * altPrunedEditBound κ η := by
    have he := matrixDoubledTuple_perturb_sq_le U W T
    have hs := mul_le_mul_of_nonneg_left hsumξ (show (0 : ℝ) ≤ 2 * h by positivity)
    have hb := mul_le_mul_of_nonneg_left htracebound (show (0 : ℝ) ≤ 16 * h by positivity)
    have hw := mul_le_mul_of_nonneg_left hWdist (by norm_num : (0 : ℝ) ≤ 4)
    unfold altPrunedEditBound
    nlinarith only [he, hdist, hs, hb, hw]
  refine ⟨{
    n := sel.n, length_le := sel.length_le, E := E, T := T,
    projection := hE, orthogonal := hEorth, sum_one := hEsum,
    reducing := hred, bad_identity := hbad, bad_trace := htracebound,
    perturbation := hdistbound, scalar_gap := ?_ }⟩
  intro i hi X hleft hright
  have he := hgap i hi X hleft hright
  convert he using 1
  ring

end ThomGame.Analysis
