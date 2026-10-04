module

public import ThomGame.Analysis.PositiveTracialProducts
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Positivity and faithfulness for trace projections

A star-preserving linear projection with the trace pairing onto a closed
star subalgebra is positive. Negative-part functional calculus makes
this implication explicit. Faithful positive traces also separate
comparable elements, as needed for normality of trace-preserving maps.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem eq_zero_of_nonneg_of_faithful_trace
    (τ : A →ₗ[ℝ] ℝ) (hfaith : ∀ a, τ (star a * a) = 0 → a = 0)
    (a : A) (ha : 0 ≤ a) (hτa : τ a = 0) : a = 0 := by
  have hs := (CFC.sqrt_nonneg a).isSelfAdjoint
  have hz : CFC.sqrt a = 0 := by
    apply hfaith
    rw [hs.star_eq, CFC.sqrt_mul_sqrt_self a ha, hτa]
  rw [← CFC.sqrt_mul_sqrt_self a ha, hz, zero_mul]

theorem eq_of_le_of_faithful_trace
    (τ : A →ₗ[ℝ] ℝ) (hfaith : ∀ a, τ (star a * a) = 0 → a = 0)
    (a b : A) (hab : a ≤ b) (hτ : τ a = τ b) : a = b := by
  apply (sub_eq_zero.mp (eq_zero_of_nonneg_of_faithful_trace τ hfaith (b - a)
    (sub_nonneg.mpr hab) ?_)).symm
  rw [map_sub, hτ, sub_self]

theorem trace_projection_nonneg
    (τ : A →ₗ[ℝ] ℝ) (hpos : ∀ a, 0 ≤ a → 0 ≤ τ a)
    (hcyc : ∀ a b, τ (a * b) = τ (b * a))
    (hfaith : ∀ a, τ (star a * a) = 0 → a = 0)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (E : A →ₗ[ℂ] A)
    (hmem : ∀ a, E a ∈ S) (hstar : ∀ a, E (star a) = star (E a))
    (hpair : ∀ a b, b ∈ S → τ (star b * E a) = τ (star b * a))
    (a : A) (ha : 0 ≤ a) : 0 ≤ E a := by
  have hE : IsSelfAdjoint (E a) := by
    change star (E a) = E a
    rw [← hstar, ha.isSelfAdjoint.star_eq]
  have hn : (E a)⁻ ∈ S := cfcₙ_mem (𝕜' := ℂ) (·⁻ : ℝ → ℝ) (hmem a)
  have hns := (CFC.negPart_nonneg (E a)).isSelfAdjoint
  have hp := positive_trace_mul_nonneg τ hpos hcyc (E a)⁻ a (CFC.negPart_nonneg _) ha
  have heq := hpair a (E a)⁻ hn
  rw [hns.star_eq] at heq
  rw [← heq] at hp
  have hmul : (E a)⁻ * E a = -(star (E a)⁻ * (E a)⁻) := by
    calc
      (E a)⁻ * E a = (E a)⁻ * ((E a)⁺ - (E a)⁻) :=
        congrArg ((E a)⁻ * ·) (CFC.posPart_sub_negPart (E a) hE).symm
      _ = -(star (E a)⁻ * (E a)⁻) := by
        rw [mul_sub, CFC.negPart_mul_posPart, zero_sub, hns.star_eq]
  rw [hmul, map_neg, neg_nonneg] at hp
  exact (CFC.negPart_eq_zero_iff (E a) hE).mp
    (hfaith _ (le_antisymm hp (hpos _ (star_mul_self_nonneg _))))

theorem norm_le_of_unital_schwarz [Nontrivial A] (E : A →ₚ[ℂ] A) (hone : E 1 = 1)
    (hschwarz : ∀ a, star (E a) * E a ≤ E (star a * a)) (a : A) : ‖E a‖ ≤ ‖a‖ := by
  have hp := E.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a)
  rw [hone, norm_one, one_mul] at hp
  have h := (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hschwarz a) (star_mul_self_nonneg _)).trans hp
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa only [sq] using h)

end ThomGame.Analysis
