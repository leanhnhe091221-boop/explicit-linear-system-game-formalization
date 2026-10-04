module

public import ThomGame.Analysis.MatrixProjectionMixing
public import ThomGame.Analysis.MatrixExponentialRangeDerivative
public import ThomGame.Analysis.UniformIntervalParts

/-!
# Trace derivatives and interval averaging of exponential ranges

The exact local identity from ALT Lemma 3.4 is proved for the actual
range projection, then integrated with the uniform interval weight.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixExponentialRange_continuous {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : Matrix.IsHermitian E) (hAE : Commute A E)
    (Y : Matrix ι κ ℂ) (t : ℝ) : Continuous (fun a : ℝ => matrixExponentialRange t (A + a • E) Y) :=
  continuous_iff_continuousAt.mpr fun s => (matrixExponentialRange_hasDerivAt hA hE hAE Y t s).continuousAt

theorem matrixExponentialRange_trace_hasDerivAt (r : Nat) {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : IsStarProjection E) (hAE : Commute A E)
    (Y : Matrix ι κ ℂ) (t s : ℝ) :
    HasDerivAt (fun a => matrixTraceReal r (E * matrixExponentialRange t (A + a • E) Y))
      (2 * t * matrixProjectionMixing r E (matrixExponentialRange t (A + s • E) Y)) s := by
  have hp := matrixExponentialRange_hasDerivAt hA hE.isSelfAdjoint.isHermitian hAE Y t s
  have he := matrixTraceReal_hasDerivAt r
    (rectangular_mul_hasDerivAt (hasDerivAt_const s E) hp)
  simpa only [Matrix.zero_mul, zero_add, matrixTraceReal_projection_tangent r hE] using! he

theorem matrixExponentialMixing_continuous (r : Nat) {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : Matrix.IsHermitian E) (hAE : Commute A E)
    (Y : Matrix ι κ ℂ) (t : ℝ) :
    Continuous (fun a : ℝ => matrixProjectionMixing r E (matrixExponentialRange t (A + a • E) Y)) :=
  (matrixProjectionMixing_continuous r E).comp (matrixExponentialRange_continuous hA hE hAE Y t)

theorem matrixExponentialMixing_interval_identity (r : Nat) {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : IsStarProjection E) (hAE : Commute A E)
    (Y : Matrix ι κ ℂ) (t : ℝ) :
    t * (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) *
      matrixProjectionMixing r E (matrixExponentialRange t (A + s • E) Y)) =
    ∫ s in (-1 : ℝ)..1, s * matrixTraceReal r (E * matrixExponentialRange t (A + s • E) Y) := by
  have hc := (matrixExponentialMixing_continuous r hA hE.isSelfAdjoint.isHermitian hAE Y t).const_mul (2 * t)
  have he := uniform_interval_integration_by_parts
    (fun s => matrixExponentialRange_trace_hasDerivAt r hA hE hAE Y t s) hc
  have hi : (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) *
      (2 * t * matrixProjectionMixing r E (matrixExponentialRange t (A + s • E) Y))) =
      (2 * t) * (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) *
      matrixProjectionMixing r E (matrixExponentialRange t (A + s • E) Y)) := by
    simp only [mul_left_comm (1 - _ ^ 2) (2 * t), intervalIntegral.integral_const_mul]
  rw [hi] at he
  linarith

end ThomGame.Analysis
