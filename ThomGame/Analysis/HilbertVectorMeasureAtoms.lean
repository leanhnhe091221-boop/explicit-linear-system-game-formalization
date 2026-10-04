module

public import ThomGame.Analysis.HilbertVectorMeasure
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-! Vanishing atoms of vector measures from the mean ergodic theorem. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Set MeasureTheory Filter
open scoped BigOperators Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def continuousCesaro (f : C(X, ℂ)) (n : ℕ) : C(X, ℂ) :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, f ^ k

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem continuousCesaro_at_one (f : C(X, ℂ)) (x : X) (hf : f x = 1) (n : ℕ) (hn : n ≠ 0) :
    continuousCesaro f n x = 1 := by
  simp [continuousCesaro, hf, hn]

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem hilbertCalculus_pow_apply (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (f : C(X, ℂ))
    (n : ℕ) (ξ : H) : π (f ^ n) ξ = (π f)^[n] ξ := by
  rw [map_pow]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Function.iterate_succ_apply']
      exact congrArg (π f) ih

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem hilbertCalculus_cesaro_apply (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (f : C(X, ℂ))
    (n : ℕ) (ξ : H) :
    π (continuousCesaro f n) ξ = birkhoffAverage ℂ (π f) id n ξ := by
  simp only [continuousCesaro, map_smul, map_sum, smul_apply, sum_apply,
    hilbertCalculus_pow_apply, birkhoffAverage, birkhoffSum, id_eq]

theorem hilbertVectorMeasure_atom_le_normSq (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (f : C(X, ℂ)) (x : X) (hf : f x = 1) :
    (hilbertVectorMeasure π ξ).real {x} ≤ ‖π f ξ‖ ^ 2 := by
  have hi : Integrable (fun y => ‖f y‖ ^ 2) (hilbertVectorMeasure π ξ) :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := hi.measure_le_integral (ae_of_all _ fun y => sq_nonneg ‖f y‖)
    (s := {x}) (fun y hy => by rcases Set.mem_singleton_iff.mp hy with rfl; simp [hf])
  rw [hilbertVectorMeasure_integral_normSq] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  exact hr

theorem hilbertVectorMeasure_atom_zero_of_orthogonal
    (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C(X, ℂ)) (x : X)
    (hf : f x = 1) (hπ : ‖π f‖ ≤ 1)
    (hξ : ξ ∈ ((π f).eqLocus (1 : H →L[ℂ] H))ᗮ) :
    (hilbertVectorMeasure π ξ).real {x} = 0 := by
  have hmean := (π f).tendsto_birkhoffAverage_orthogonalProjection hπ ξ
  have hp : ((π f).eqLocus (1 : H →L[ℂ] H)).orthogonalProjectionOnto ξ = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hξ
  have hm : Tendsto (fun n => π (continuousCesaro f n) ξ) atTop (𝓝 (0 : H)) := by
    simpa only [hilbertCalculus_cesaro_apply, hp, Submodule.coe_zero] using hmean
  have hn : Tendsto (fun n => ‖π (continuousCesaro f n) ξ‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using hm.norm.pow 2
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto hn
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact hilbertVectorMeasure_atom_le_normSq π ξ (continuousCesaro f n) x
    (continuousCesaro_at_one f x hf n (by omega))

end ThomGame.Analysis
