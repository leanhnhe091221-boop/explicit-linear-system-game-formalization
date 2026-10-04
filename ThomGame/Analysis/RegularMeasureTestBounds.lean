module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Tactic

/-! Quantitative continuous-test inequalities extend to all Borel sets for regular measures. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

theorem measureReal_compact_le_of_continuous_integral_le
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.OuterRegular]
    (C : ℝ)
    (htest : ∀ f : C(X, ℝ), (∀ x, f x ∈ Icc 0 1) →
      (∫ x, f x ∂μ) ≤ (∫ x, f x ∂ν) + C)
    (K : Set X) (hK : IsCompact K) : μ.real K ≤ ν.real K + C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨V, hKV, hV, hνV⟩ := K.exists_isOpen_le_add ν
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hνVr : ν.real V ≤ ν.real K + ε := by
    have h := ENNReal.toReal_mono (by finiteness) hνV
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hε.le] at h
    exact h
  obtain ⟨f, hfK, _, hfV, hf⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  have hfiμ : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfiν : Integrable f ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKf : ∀ x, K.indicator (fun _ => (1 : ℝ)) x ≤ f x := by
    intro x
    by_cases hx : x ∈ K
    · simp [hx, hfK hx]
    · simp [hx, (hf x).1]
  have hfV' : ∀ x, f x ≤ V.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · simp [hfV hx, (hf x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hlo : μ.real K ≤ ∫ x, f x ∂μ := by
    rw [← integral_indicator_one hK.measurableSet]
    exact integral_mono ((integrable_const (1 : ℝ)).indicator hK.measurableSet) hfiμ hKf
  have hhi : (∫ x, f x ∂ν) ≤ ν.real V := by
    rw [← integral_indicator_one hV.measurableSet]
    exact integral_mono hfiν ((integrable_const (1 : ℝ)).indicator hV.measurableSet) hfV'
  have hmid := htest f hf
  linarith

theorem measureReal_borel_le_of_continuous_integral_le
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.InnerRegular] [ν.OuterRegular]
    (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ f : C(X, ℝ), (∀ x, f x ∈ Icc 0 1) →
      (∫ x, f x ∂μ) ≤ (∫ x, f x ∂ν) + C)
    (s : Set X) (hs : MeasurableSet s) : μ.real s ≤ ν.real s + C := by
  have hcompact (K : Set X) (hK : IsCompact K) : μ K ≤ ν K + ENNReal.ofReal C := by
    have h := ENNReal.ofReal_le_ofReal
      (measureReal_compact_le_of_continuous_integral_le μ ν C htest K hK)
    rw [ENNReal.ofReal_add measureReal_nonneg hC] at h
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have h : μ s ≤ ν s + ENNReal.ofReal C := by
    rw [hs.measure_eq_iSup_isCompact μ]
    refine iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
    exact (hcompact K hK).trans (add_le_add (measure_mono hKs) le_rfl)
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hC] at hr
  exact hr

end ThomGame.Analysis
