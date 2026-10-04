module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The actual uniform measure on a finite cube

Each coordinate has normalized Lebesgue measure on [-1,1]. The
finite product is a probability measure supported on the compact cube.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped ENNReal

noncomputable def uniformIntervalMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)

instance uniformIntervalMeasure_probability : IsProbabilityMeasure uniformIntervalMeasure := by
  constructor
  norm_num [uniformIntervalMeasure, Measure.smul_apply, Measure.restrict_apply,
    Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem uniformIntervalMeasure_ae : ∀ᵐ a ∂uniformIntervalMeasure, a ∈ Icc (-1 : ℝ) 1 := by
  exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)).mpr
    (ae_restrict_mem measurableSet_Icc)

theorem uniformIntervalMeasure_integral (f : ℝ → ℝ) :
    (∫ a, f a ∂uniformIntervalMeasure) = (1 / 2 : ℝ) * ∫ a in (-1 : ℝ)..1, f a := by
  rw [uniformIntervalMeasure, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

variable {μ : Type*} [Fintype μ]

noncomputable def uniformCubeMeasure : Measure (μ → ℝ) :=
  Measure.pi (fun _ => uniformIntervalMeasure)

instance uniformCubeMeasure_probability :
    IsProbabilityMeasure (uniformCubeMeasure (μ := μ)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : μ => uniformIntervalMeasure)))

def uniformCube : Set (μ → ℝ) := univ.pi (fun _ => Icc (-1 : ℝ) 1)

omit [Fintype μ] in
theorem mem_uniformCube {s : μ → ℝ} : s ∈ uniformCube ↔ ∀ i, |s i| ≤ 1 := by
  simp only [uniformCube, mem_pi, mem_univ, forall_true_left, mem_Icc, abs_le]

omit [Fintype μ] in
theorem uniformCube_isCompact : IsCompact (uniformCube (μ := μ)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem uniformCubeMeasure_ae : ∀ᵐ s ∂(uniformCubeMeasure (μ := μ)), s ∈ uniformCube := by
  have he : ∀ i : μ, ∀ᵐ s ∂(uniformCubeMeasure (μ := μ)), s i ∈ Icc (-1 : ℝ) 1 :=
    fun _ => Measure.tendsto_eval_ae_ae.eventually uniformIntervalMeasure_ae
  simpa only [uniformCube, mem_pi, mem_univ, forall_true_left] using ae_all_iff.mpr he

theorem uniformCube_integrable {f : (μ → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f uniformCubeMeasure := by
  have hi := hf.continuousOn.integrableOn_compact (μ := uniformCubeMeasure) uniformCube_isCompact
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem uniformCubeMeasure_ae] at hi

end ThomGame.Analysis
