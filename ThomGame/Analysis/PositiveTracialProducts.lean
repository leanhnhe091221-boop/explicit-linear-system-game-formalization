module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Products under a positive trace

A positive real linear functional which is tracial is nonnegative on
products of positive elements, even when those elements do not commute.
The proof uses a positive square root and cyclicity.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positive_trace_mul_nonneg (τ : A →ₗ[ℝ] ℝ)
    (hpos : ∀ a : A, 0 ≤ a → 0 ≤ τ a) (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ τ (a * b) := by
  have hs : CFC.sqrt a * b * CFC.sqrt a = CFC.sqrt a * b * star (CFC.sqrt a) := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq]
  have hp := hpos _ (hs ▸ star_right_conjugate_nonneg hb (CFC.sqrt a))
  have he : τ (CFC.sqrt a * b * CFC.sqrt a) = τ (a * b) := by
    rw [hcyc (CFC.sqrt a * b) (CFC.sqrt a), ← mul_assoc, CFC.sqrt_mul_sqrt_self a ha]
  exact he ▸ hp

end ThomGame.Analysis
