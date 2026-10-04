module

public import ThomGame.Analysis.MatrixProjectionRangeColumn
public import ThomGame.Analysis.MatrixSingularValueClampEnergy

/-!
# The clipped projection column and its exact coverage defect

This constructs C from the actual projection column and identifies
the residual trace with ALT's previously defined coverage defect.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ ι κ : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
  [DecidableEq μ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype μ] [DecidableEq μ] [DecidableEq ι] in
theorem matrixRectClamp_residual (X : Matrix ι κ ℂ) :
    1 - matrixRectAbs (matrixRectClamp X) = (1 - matrixRectAbs X)⁺ := by
  let A := matrixRectAbs X
  have hA : IsSelfAdjoint A := (matrixRectAbs_nonneg X).isSelfAdjoint
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  have hsub : cfc (fun t : ℝ => 1 - t) A = 1 - A := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      hid, cfc_const_one ℝ A hA]
  rw [matrixRectClamp_abs, CFC.posPart_def, cfcₙ_eq_cfc]
  change 1 - cfc (fun t : ℝ => min t 1) A = cfc (fun t : ℝ => max t 0) (1 - A)
  rw [← hsub, ← cfc_comp' (fun t : ℝ => max t 0) (fun t : ℝ => 1 - t) A
    ((A.finite_real_spectrum.image (fun t : ℝ => 1 - t)).continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA]
  calc
    _ = cfc (fun t : ℝ => 1 - min t 1) A := by
      rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
        cfc_const_one ℝ A hA]
    _ = _ := by
      apply cfc_congr
      intro t _
      change 1 - min t 1 = max (1 - t) 0
      by_cases ht : t ≤ 1
      · rw [min_eq_left ht, max_eq_left (sub_nonneg.mpr ht)]
      · rw [min_eq_right (le_of_not_ge ht), sub_self, max_eq_right (sub_nonpos.mpr (le_of_not_ge ht))]

omit [Fintype κ] [DecidableEq μ] [DecidableEq κ] in
noncomputable def matrixClippedProjectionColumn {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) : Matrix (MatrixProjectionSumIndex hq) ι ℂ :=
  matrixRectClamp (matrixProjectionColumn hq)

omit [Fintype κ] [DecidableEq μ] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_abs {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) :
    matrixRectAbs (matrixClippedProjectionColumn hq) =
      cfc (fun t : ℝ => min t 1) (CFC.sqrt (∑ i, q i)) := by
  rw [matrixClippedProjectionColumn, matrixRectClamp_abs, matrixRectAbs, matrixProjectionColumn_gram]

omit [Fintype κ] [DecidableEq μ] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_contraction {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) :
    (matrixClippedProjectionColumn hq)ᴴ * matrixClippedProjectionColumn hq ≤ 1 :=
  matrixRectClamp_gram_le_one _

omit [Fintype κ] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_energy_le {h : Nat} (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → Matrix.unitaryGroup ι ℂ) :
    matrixIntertwiningEnergy r U (fun j => matrixProjectionBlockUnitary r hq (U j))
      (matrixClippedProjectionColumn hq) ≤ ∑ i, matrixIntertwiningEnergy r U U (q i) :=
  (matrixIntertwiningEnergy_clamp_le r U _ _).trans (matrixProjectionColumn_energy_le r hq U)

omit [Fintype ι] [Fintype κ] [DecidableEq μ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_residual {d : Nat} {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) :
    1 - matrixRectAbs (matrixClippedProjectionColumn hq) = matrixCoverageResidual (∑ i, q i) := by
  rw [matrixClippedProjectionColumn, matrixRectClamp_residual, matrixRectAbs,
    matrixProjectionColumn_gram]
  rfl

omit [Fintype ι] [Fintype κ] [DecidableEq μ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_defect {d : Nat} {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) :
    matrixTraceReal d ((1 - matrixRectAbs (matrixClippedProjectionColumn hq)) ^ 2) =
      matrixFamilyCoverageDefect q := by
  rw [matrixClippedProjectionColumn_residual]
  exact (normalizedTrace_re _).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixClippedProjectionColumn_ALT_setup {d h : Nat} [NeZero d]
    {q : μ → CMatrix d} (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s) :
    Fintype.card (MatrixProjectionSumIndex hq) ≤ 3 * d ∧
    (matrixClippedProjectionColumn hq)ᴴ * matrixClippedProjectionColumn hq ≤ 1 ∧
    matrixIntertwiningEnergy d U (fun j => matrixProjectionBlockUnitary d hq (U j))
      (matrixClippedProjectionColumn hq) ≤ s ∧
    matrixTraceReal d ((1 - matrixRectAbs (matrixClippedProjectionColumn hq)) ^ 2) =
      matrixFamilyCoverageDefect q := by
  refine ⟨matrixProjectionSumIndex_card_le_three hq htrace,
    matrixClippedProjectionColumn_contraction hq, ?_, matrixClippedProjectionColumn_defect hq⟩
  exact (matrixClippedProjectionColumn_energy_le d hq U).trans henergy

end ThomGame.Analysis
