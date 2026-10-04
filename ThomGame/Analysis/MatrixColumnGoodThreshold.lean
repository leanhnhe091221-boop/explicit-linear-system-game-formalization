module

public import ThomGame.Analysis.MatrixThresholdEnergy
public import ThomGame.Analysis.MatrixALTOrthogonalizationLemma

/-!
# A common good threshold and block correction for the actual column

The integral estimate selects one threshold that preserves both
energy and coverage. Applying the proved Lemma 3.4 yields an actual
partial isometry with block-commuting range and the required bounds.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {h : Nat}

theorem exists_matrixThresholdPolar_energy_le [NeZero h] (r : Nat)
    (hdim : Fintype.card ι + Fintype.card κ ≤ 4 * r)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) {a : ℝ} (ha : 0 < a) :
    ∃ b ∈ Icc a (2 * a), matrixIntertwiningEnergy r U V (matrixThresholdPolar X b) ≤
      2 * Real.sqrt (matrixIntertwiningEnergy r U V X) / a := by
  have hab : a < 2 * a := by linarith
  obtain ⟨b, hb, henergy⟩ := exists_le_intervalIntegral_average hab
    (matrixIntertwiningEnergy_threshold_intervalIntegrable r U V X a (2 * a))
  rw [show 2 * a - a = a by ring] at henergy
  refine ⟨b, hb, henergy.trans ?_⟩
  exact div_le_div_of_nonneg_right
    (matrixThresholdPolar_energy_coarea r hdim U V X a (2 * a) ha.le hab.le) ha.le

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem exists_matrixClippedColumn_good_threshold {μ : Type*} [Fintype μ] [DecidableEq μ]
    {d : Nat} [NeZero d] [NeZero h] {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s a : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s) (ha : 0 < a) :
    ∃ b ∈ Icc a (2 * a),
      IsStarProjection ((matrixThresholdPolar (matrixClippedProjectionColumn hq) b)ᴴ *
        matrixThresholdPolar (matrixClippedProjectionColumn hq) b) ∧
      matrixIntertwiningEnergy d U (fun j => matrixProjectionBlockUnitary d hq (U j))
        (matrixThresholdPolar (matrixClippedProjectionColumn hq) b) ≤ 2 * Real.sqrt s / a ∧
      matrixTraceReal d (1 - (matrixThresholdPolar (matrixClippedProjectionColumn hq) b)ᴴ *
        matrixThresholdPolar (matrixClippedProjectionColumn hq) b) ≤ matrixFamilyCoverageDefect q + 4 * a := by
  have hdim := matrixProjectionSumIndex_card_le_three hq htrace
  have htotal : Fintype.card (MatrixProjectionSumIndex hq) + Fintype.card (Fin d) ≤ 4 * d := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨b, hb, hbe⟩ := exists_matrixThresholdPolar_energy_le d htotal U
    (fun j => matrixProjectionBlockUnitary d hq (U j)) (matrixClippedProjectionColumn hq) ha
  have hb0 : 0 < b := ha.trans_le hb.1
  refine ⟨b, hb, matrixThresholdPolar_partialIsometry _ hb0, ?_, ?_⟩
  · refine hbe.trans (div_le_div_of_nonneg_right ?_ ha.le)
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt ((matrixClippedProjectionColumn_energy_le d hq U).trans henergy)) (by norm_num)
  · have ht := matrixThresholdPolar_clippedColumn_coverage hq hb0
    linarith [hb.2]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem exists_matrixColumn_block_partialIsometry {μ : Type*} [Fintype μ] [DecidableEq μ]
    {d : Nat} [NeZero d] [NeZero h] {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s a t : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s) (ha : 0 < a) (ht : 1 ≤ t) :
    ∃ Z : Matrix (MatrixProjectionSumIndex hq) (Fin d) ℂ,
      IsStarProjection (Zᴴ * Z) ∧
      (∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i)) ∧
      matrixIntertwiningEnergy d U (fun j => matrixProjectionBlockUnitary d hq (U j)) Z ≤
        4 * Real.exp (4 * t) * Real.sqrt s / a + 32 * t ^ (-(1 / 2 : ℝ)) ∧
      matrixTraceReal d (1 - Zᴴ * Z) ≤ matrixFamilyCoverageDefect q + 4 * a := by
  obtain ⟨b, _, hY, hYe, hYcov⟩ := exists_matrixClippedColumn_good_threshold hq U htrace henergy ha
  let E := fun i => matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i
  have hdim : Fintype.card (MatrixProjectionSumIndex hq) ≤ 3 * Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    exact matrixProjectionSumIndex_card_le_three hq htrace
  obtain ⟨Z, hZ, hZi, hZcomm, hZe⟩ := exists_matrixPartialIsometry_ALT_lemma3_4 U
    (fun j => matrixProjectionBlockUnitary d hq (U j)) E
    (fun i => matrixBlockLabel_projection i) (fun i j hij => matrixBlockLabel_orthogonal hij)
    matrixBlockLabel_sum hdim (fun j i => (matrixProjectionBlockUnitary_commute d hq (U j) i).eq) hY ht
  rw [Fintype.card_fin] at hZe
  refine ⟨Z, hZ, hZcomm, ?_, ?_⟩
  · calc
      _ ≤ 2 * Real.exp (4 * t) * (2 * Real.sqrt s / a) + 32 * t ^ (-(1 / 2 : ℝ)) :=
        hZe.trans (add_le_add (mul_le_mul_of_nonneg_left hYe (by positivity)) le_rfl)
      _ = _ := by ring
  · rw [hZi]
    exact hYcov

end ThomGame.Analysis
