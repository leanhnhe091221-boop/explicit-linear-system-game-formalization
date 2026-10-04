module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt

/-!
# A root-mean-square bound for finite averages

A pointwise bound `f <= c g + beta` with nonnegative data passes to
the corresponding second moments. Finite Cauchy--Schwarz controls
the average of `g`; the additive error remains exactly `beta`.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem finite_expect_le_sqrt_expect_sq (g : Ω → ℝ) :
    (𝔼 ω, g ω) ≤ Real.sqrt (𝔼 ω, g ω ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [mul_one, one_pow, Fintype.expect_const] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ g (fun _ => (1 : ℝ))

theorem sqrt_expect_sq_le_of_pointwise (f g : Ω → ℝ) (c β : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hfg : ∀ ω, f ω ≤ c * g ω + β) :
    Real.sqrt (𝔼 ω, f ω ^ 2) ≤ c * Real.sqrt (𝔼 ω, g ω ^ 2) + β := by
  have he : (𝔼 ω, f ω ^ 2) ≤ 𝔼 ω, (c * g ω + β) ^ 2 := by
    apply Finset.expect_le_expect
    intro ω _
    exact sq_le_sq₀ (hf ω) (add_nonneg (mul_nonneg hc (hg ω)) hβ) |>.2 (hfg ω)
  have heq : (𝔼 ω, (c * g ω + β) ^ 2) =
      c ^ 2 * (𝔼 ω, g ω ^ 2) + 2 * c * β * (𝔼 ω, g ω) + β ^ 2 := by
    calc
      _ = 𝔼 ω, (c ^ 2 * g ω ^ 2 + (2 * c * β) * g ω + β ^ 2) :=
        Finset.expect_congr rfl fun ω _ => by ring
      _ = _ := by simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  rw [heq] at he
  have hsq : Real.sqrt (𝔼 ω, g ω ^ 2) ^ 2 = 𝔼 ω, g ω ^ 2 :=
    Real.sq_sqrt (Finset.expect_nonneg fun ω _ => sq_nonneg _)
  have hg' := mul_le_mul_of_nonneg_left (finite_expect_le_sqrt_expect_sq g)
    (show 0 ≤ 2 * c * β by positivity)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

end ThomGame.Analysis
