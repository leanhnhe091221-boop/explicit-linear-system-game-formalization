module

public import ThomGame.Analysis.UniformBoundary
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Weighted mixing estimates and an actual good cube parameter

Combining the interior weight with the exact boundary probabilities
turns a weighted expectation into an unweighted one. Selection is
inside the cube, including when the parameter index type is empty.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory

variable {μ : Type*} [Fintype μ]

theorem uniformCube_exists_le_integral {f : (μ → ℝ) → ℝ} (hf : Continuous f) :
    ∃ s ∈ uniformCube, f s ≤ ∫ a, f a ∂uniformCubeMeasure := by
  obtain ⟨s, hs, hf⟩ := exists_notMem_null_le_integral
    (uniformCube_integrable hf) (ae_iff.mp (uniformCubeMeasure_ae (μ := μ)))
  exact ⟨s, by simpa using hs, hf⟩

theorem uniformCube_mixing_expectation_le (m : μ → (μ → ℝ) → ℝ) (M : μ → ℝ)
    (hc : ∀ j, Continuous (m j))
    (hm : ∀ s ∈ uniformCube, ∀ j, 0 ≤ m j s)
    (hM : ∀ s ∈ uniformCube, ∀ j, m j s ≤ M j)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hweighted : t * (∫ s, ∑ j, (1 - (s j) ^ 2) * m j s ∂uniformCubeMeasure) ≤ 1) :
    (∫ s, ∑ j, m j s ∂uniformCubeMeasure) ≤ (t * ε)⁻¹ + ε * ∑ j, M j := by
  have hi (j : μ) : Integrable (fun s => (1 - (s j) ^ 2) * m j s) uniformCubeMeasure :=
    uniformCube_integrable (by fun_prop)
  have hb (j : μ) : Integrable (fun s => M j * uniformBoundaryWeight ε (s j)) uniformCubeMeasure :=
    (uniformCube_boundary_integrable ε j).const_mul _
  have hsum : Integrable (fun s => ∑ j, (1 - (s j) ^ 2) * m j s) uniformCubeMeasure :=
    uniformCube_integrable (by fun_prop)
  have hbsum : Integrable (fun s : μ → ℝ => ∑ j, M j * uniformBoundaryWeight ε (s j)) uniformCubeMeasure :=
    integrable_finsetSum _ (fun j _ => hb j)
  calc
    _ ≤ ∫ s, ε⁻¹ * (∑ j, (1 - (s j) ^ 2) * m j s) +
        ∑ j, M j * uniformBoundaryWeight ε (s j) ∂uniformCubeMeasure := by
      apply integral_mono_ae (uniformCube_integrable (by fun_prop))
        ((hsum.const_mul _).add hbsum)
      filter_upwards [uniformCubeMeasure_ae] with s hs
      dsimp only [Pi.add_apply]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun j _ => uniformBoundary_weighted_bound hε hε1
        (mem_uniformCube.mp hs j) (hm s hs j) (hM s hs j))
    _ = ε⁻¹ * (∫ s, ∑ j, (1 - (s j) ^ 2) * m j s ∂uniformCubeMeasure) + ε * ∑ j, M j := by
      rw [integral_add (hsum.const_mul _) hbsum, integral_const_mul,
        integral_finsetSum _ (fun j _ => hb j)]
      simp_rw [integral_const_mul, uniformCube_boundary_integral hε.le hε1,
        ← Finset.sum_mul]
      rw [mul_comm (∑ j, M j) ε]
    _ ≤ _ := by
      have hw : (∫ s, ∑ j, (1 - (s j) ^ 2) * m j s ∂uniformCubeMeasure) ≤ t⁻¹ := by
        simpa only [mul_one] using (le_inv_mul_iff₀ ht).mpr hweighted
      have he := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hε.le)
      rw [mul_inv_rev]
      exact add_le_add he le_rfl

end ThomGame.Analysis
