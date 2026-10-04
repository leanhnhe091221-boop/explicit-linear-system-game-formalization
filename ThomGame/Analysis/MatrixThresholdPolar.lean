module

public import ThomGame.Analysis.MatrixClippedProjectionColumn

/-!
# Actual threshold polar factors and their coverage bound

For b > 0, restrict the polar factor to singular values at least b.
The initial projection is exactly the closed upper spectral cut.
For the clipped projection column the lost trace is at most delta(q)+2b.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def matrixUpperSpectralProjection (A : Matrix κ κ ℂ) (b : ℝ) : Matrix κ κ ℂ :=
  cfc (spectralStep b) A

omit [Fintype ι] [DecidableEq ι] in
theorem matrixUpperSpectralProjection_projection (A : Matrix κ κ ℂ) (b : ℝ) :
    IsStarProjection (matrixUpperSpectralProjection A b) := by
  constructor
  · show matrixUpperSpectralProjection A b * matrixUpperSpectralProjection A b = _
    rw [matrixUpperSpectralProjection, ← cfc_mul _ _ A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro t _
    exact (pow_two _).symm.trans (spectralStep_sq _ _)
  · exact IsSelfAdjoint.cfc

omit [Fintype ι] [DecidableEq ι] in
theorem matrixRealSupport_mul_upperSpectralProjection (A : Matrix κ κ ℂ) {b : ℝ} (hb : 0 < b) :
    matrixRealSupport A * matrixUpperSpectralProjection A b = matrixUpperSpectralProjection A b := by
  rw [matrixRealSupport, matrixUpperSpectralProjection, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  by_cases ht : t = 0
  · simp [ht, spectralStep, not_le_of_gt hb]
  · simp [ht]

omit [DecidableEq ι] in
noncomputable def matrixThresholdPolar (X : Matrix ι κ ℂ) (b : ℝ) : Matrix ι κ ℂ :=
  matrixRectPolar X * matrixUpperSpectralProjection (matrixRectAbs X) b

omit [DecidableEq ι] in
theorem matrixThresholdPolar_initial (X : Matrix ι κ ℂ) {b : ℝ} (hb : 0 < b) :
    (matrixThresholdPolar X b)ᴴ * matrixThresholdPolar X b =
      matrixUpperSpectralProjection (matrixRectAbs X) b := by
  have hQ := matrixUpperSpectralProjection_projection (matrixRectAbs X) b
  rw [matrixThresholdPolar, Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq]
  calc
    _ = matrixUpperSpectralProjection (matrixRectAbs X) b *
        ((matrixRectPolar X)ᴴ * matrixRectPolar X) * matrixUpperSpectralProjection (matrixRectAbs X) b := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [matrixRectPolar_initial, Matrix.mul_assoc, matrixRealSupport_mul_upperSpectralProjection _ hb,
        hQ.isIdempotentElem.eq]

omit [DecidableEq ι] in
theorem matrixThresholdPolar_partialIsometry (X : Matrix ι κ ℂ) {b : ℝ} (hb : 0 < b) :
    IsStarProjection ((matrixThresholdPolar X b)ᴴ * matrixThresholdPolar X b) := by
  rw [matrixThresholdPolar_initial X hb]
  exact matrixUpperSpectralProjection_projection _ _

omit [DecidableEq ι] in
theorem matrixThresholdPolar_initial_closed_interval (X : Matrix ι κ ℂ) {b : ℝ} (hb : 0 < b)
    (hX : matrixRectAbs X ≤ 1) :
    (matrixThresholdPolar X b)ᴴ * matrixThresholdPolar X b =
      cfc (fun t : ℝ => if b ≤ t ∧ t ≤ 1 then 1 else 0) (matrixRectAbs X) := by
  rw [matrixThresholdPolar_initial X hb, matrixUpperSpectralProjection]
  apply cfc_congr
  intro t ht
  have ht1 := (CFC.le_one_iff (R := ℝ) _ (matrixRectAbs_nonneg X).isSelfAdjoint).mp hX t ht
  simp only [spectralStep, ht1, and_true]

theorem spectralStep_complement_le_square {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    1 - spectralStep b t ≤ (1 - t) ^ 2 + 2 * b := by
  by_cases ht : b ≤ t
  · simp only [spectralStep, ite_eq_left ht, sub_self]
    positivity
  · simp only [spectralStep, ite_eq_right ht, sub_zero]
    nlinarith [sq_nonneg t, lt_of_not_ge ht]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixUpperSpectralProjection_complement_le {A : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) {b : ℝ} (hb : 0 ≤ b) :
    1 - matrixUpperSpectralProjection A b ≤ (1 - A) ^ 2 + (2 * b) • (1 : Matrix κ κ ℂ) := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  have hsub : cfc (fun t : ℝ => 1 - t) A = 1 - A := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA.isSelfAdjoint, hid]
  have hl : cfc (fun t : ℝ => 1 - spectralStep b t) A = 1 - matrixUpperSpectralProjection A b := by
    rw [cfc_sub _ _ A (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA.isSelfAdjoint]
    rfl
  have hr : cfc (fun t : ℝ => (1 - t) ^ 2 + 2 * b) A =
      (1 - A) ^ 2 + (2 * b) • (1 : Matrix κ κ ℂ) := by
    rw [cfc_add A _ _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_pow _ 2 A (A.finite_real_spectrum.continuousOn _), hsub, cfc_const (2 * b) A hA.isSelfAdjoint]
    rw [Algebra.algebraMap_eq_smul_one]
  rw [← hl, ← hr]
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro t _
  exact spectralStep_complement_le_square hb t

omit [DecidableEq ι] in
theorem matrixThresholdPolar_lost_trace_le (r : Nat) (X : Matrix ι κ ℂ) {b : ℝ} (hb : 0 < b) :
    matrixTraceReal r (1 - (matrixThresholdPolar X b)ᴴ * matrixThresholdPolar X b) ≤
      matrixTraceReal r ((1 - matrixRectAbs X) ^ 2) +
        2 * b * matrixTraceReal r (1 : Matrix κ κ ℂ) := by
  rw [matrixThresholdPolar_initial X hb]
  have he := matrixTraceReal_mono r (matrixUpperSpectralProjection_complement_le (matrixRectAbs_isHermitian X) hb.le)
  simpa only [matrixTraceReal_add, matrixTraceReal_real_smul] using he

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixThresholdPolar_clippedColumn_coverage {μ : Type*} [Fintype μ] {d : Nat} [NeZero d]
    {q : μ → CMatrix d} (hq : ∀ i, IsStarProjection (q i)) {b : ℝ} (hb : 0 < b) :
    matrixTraceReal d (1 - (matrixThresholdPolar (matrixClippedProjectionColumn hq) b)ᴴ *
      matrixThresholdPolar (matrixClippedProjectionColumn hq) b) ≤ matrixFamilyCoverageDefect q + 2 * b := by
  have he := matrixThresholdPolar_lost_trace_le d (matrixClippedProjectionColumn hq) hb
  rw [matrixClippedProjectionColumn_defect] at he
  have hone : matrixTraceReal d (1 : CMatrix d) = 1 := by
    rw [matrixTraceReal, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, div_self]
    exact_mod_cast NeZero.ne d
  simpa only [hone, mul_one] using he

end ThomGame.Analysis
