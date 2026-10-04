module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Resampling one coordinate of an actual product probability measure

Replacing one coordinate by an independent sample preserves the
product law. Fubini consequently recovers the original expectation
by first averaging that coordinate.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (ν : Measure α) [IsProbabilityMeasure ν]

theorem measurePreserving_product_update (j : ι) :
    MeasurePreserving (fun x : (ι → α) × α => Function.update x.1 j x.2)
      ((Measure.pi (fun _ : ι => ν)).prod ν) (Measure.pi (fun _ : ι => ν)) := by
  have hm : Measurable (fun x : (ι → α) × α => Function.update x.1 j x.2) := by fun_prop
  refine ⟨hm, (Measure.pi_eq (fun S hS => ?_)).symm⟩
  rw [Measure.map_apply hm (.univ_pi hS)]
  have hp : (fun x : (ι → α) × α => Function.update x.1 j x.2) ⁻¹' (univ.pi S) =
      (univ.pi (Function.update S j univ)) ×ˢ S j := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hij : i = j
        · subst i; simp
        · simpa [Function.update_of_ne hij] using h i
      · simpa using h j
    · rintro ⟨h, hj⟩ i
      by_cases hij : i = j
      · subst i; simpa using hj
      · simpa [Function.update_of_ne hij] using h i
  rw [hp, Measure.prod_prod, Measure.pi_pi]
  have he : (fun i => ν (Function.update S j univ i)) =
      Function.update (fun i => ν (S i)) j 1 := by
    funext i
    by_cases hij : i = j
    · subst i; simp
    · simp [Function.update_of_ne hij]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_erase_mul Finset.univ (fun i => ν (S i)) (Finset.mem_univ j))

theorem integral_product_update (j : ι) {f : (ι → α) → ℝ}
    (hf : Integrable f (Measure.pi (fun _ : ι => ν))) :
    (∫ s, ∫ a, f (Function.update s j a) ∂ν ∂Measure.pi (fun _ : ι => ν)) =
      ∫ s, f s ∂Measure.pi (fun _ : ι => ν) := by
  have hm := measurePreserving_product_update (ι := ι) ν j
  have hi := hm.integrable_comp_of_integrable hf
  change Integrable (fun x : (ι → α) × α => f (Function.update x.1 j x.2)) _ at hi
  rw [← integral_prod _ hi]
  have he := integral_map hm.measurable.aemeasurable
    (hm.map_eq.symm ▸ hf.aestronglyMeasurable)
  rw [hm.map_eq] at he
  exact he.symm

end ThomGame.Analysis
